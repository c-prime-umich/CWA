# checker.jl — Julia translation of the verifier (checker.c).

using DelimitedFiles

const MAX_WAVES = 100
const L = 2.0 * π

struct Wave{T<:Real}
    A::Vector{T}
    sigma::Vector{T}
    v::Vector{T}
    Nt::Int
    theta0::T
end

mutable struct Data{W<:Wave}
    XT::Matrix{Float64}     # Nb × Nfr
    BG::Matrix{Float64}     # Nb × Nbg
    Nb::Int
    Nfr::Int
    Nbg::Int
    dt::Float64
    waves::Vector{W}
    num_waves::Int
end

range2pi(x::Float64) = x - L * floor(x / L)

wrap(x::Float64) = range2pi(x + π) - π

function interpolate_ref(f::Float64, y::Vector{Float64}, k::Real)
    j = floor(Int, k / f)                       # 0-based sample index
    frac = (k - j * f) / f
    return frac > 0.0 ? y[j + 1] + frac * (y[j + 2] - y[j + 1]) : y[j + 1]
end

function synthesize_ref!(S::AbstractMatrix{Float64}, data::Data)
    Nw  = data.num_waves
    Nb  = data.Nb
    Nfr = data.Nfr
    Nbg = data.Nbg
    dt  = data.dt
    waves = data.waves
    theta = Vector{Float64}(undef, Nw)

    for k in 0:Nfr - 1
        for i in 0:Nb - 1
            bg_col = trunc(Int, k * (Nbg - 1) / (Nfr - 1))   # mirrors C's (int) cast
            a = data.BG[i + 1, bg_col + 1]

            for w in 1:Nw
                Nt = waves[w].Nt
                f  = (Nfr - 1) / (Nt - 1)
                A     = interpolate_ref(f, waves[w].A,     k)
                sigma = interpolate_ref(f, waves[w].sigma, k)

                if k == 0
                    theta[w] = waves[w].theta0
                elseif i == 0
                    v = interpolate_ref(f, waves[w].v, k - 1)
                    theta[w] = range2pi(theta[w] + v * dt)
                end

                dx = wrap(i * (L / Nb) - theta[w])
                a += A * exp(-dx * dx / (2.0 * sigma * sigma))
            end
            S[i + 1, k + 1] = a
        end
    end
    return S
end

function synthesize_ref(data::Data)
    S = Matrix{Float64}(undef, data.Nb, data.Nfr)
    synthesize_ref!(S, data)
    return S
end

# ======================== Wave-shape kernels ========================
# kernel(dx, σ) -> unit height at angular distance dx from the wave center.

kernel_gauss(dx, σ)   = exp(-dx * dx / (2 * σ * σ))

kernel_gauss_c(dx, σ) = exp(-(dx * dx / (2.0 * (σ * σ))))

# ======================== Optimized synthesize ========================
# Computes the same values as the C `synthesize` but hoists the A/σ
# interpolation out of the pixel loop

@inline function interpolate(Nfr::Int, Nt::Int, y::AbstractVector, k::Real)
    a = (k / (Nfr - 1)) * (Nt - 1)
    j = floor(Int, a)
    yj = y[j + 1]
    return j + 1 < Nt ? ((j + 1) - a) * yj + (a - j) * y[j + 2] : yj
end

function synthesize!(S::AbstractMatrix,
                     theta_buf::AbstractVector,
                     A_buf::AbstractVector,
                     σ_buf::AbstractVector,
                     BG::AbstractMatrix,
                     waves,
                     dt::Real;
                     kernel = kernel_gauss)
    Nb, Nfr = size(S)
    Nbg = size(BG, 2)
    Nw  = length(waves)
    @assert length(theta_buf) == length(A_buf) == length(σ_buf) == Nw

    @inbounds for k in 0:Nfr - 1
        if k == 0
            for w in 1:Nw
                theta_buf[w] = waves[w].theta0
            end
        else
            for w in 1:Nw
                Nt = waves[w].Nt
                v  = interpolate(Nfr, Nt, waves[w].v, k - 1)
                theta_buf[w] = range2pi(theta_buf[w] + v * dt)
            end
        end

        for w in 1:Nw
            Nt = waves[w].Nt
            A_buf[w] = interpolate(Nfr, Nt, waves[w].A,     k)
            σ_buf[w] = interpolate(Nfr, Nt, waves[w].sigma, k)
        end

        bg_col = trunc(Int, (k / (Nfr - 1)) * (Nbg - 1))

        for i in 0:Nb - 1
            a = BG[i + 1, bg_col + 1]
            for w in 1:Nw
                dx = wrap(i * (L / Nb) - theta_buf[w])
                a += A_buf[w] * kernel(dx, σ_buf[w])
            end
            S[i + 1, k + 1] = a
        end
    end
    return S
end

function synthesize(BG::AbstractMatrix, waves, dt::Real, Nb::Int, Nfr::Int;
                    kernel = kernel_gauss)
    T = promote_type(eltype(BG), typeof(dt),
                     isempty(waves) ? Float64 : eltype(first(waves).A))
    S = Matrix{T}(undef, Nb, Nfr)
    Nw = length(waves)
    theta_buf = Vector{T}(undef, Nw)
    A_buf     = Vector{T}(undef, Nw)
    σ_buf     = Vector{T}(undef, Nw)
    synthesize!(S, theta_buf, A_buf, σ_buf, BG, waves, dt; kernel = kernel)
    return S
end

synthesize(data::Data; kernel = kernel_gauss) =
    synthesize(data.BG, data.waves, data.dt, data.Nb, data.Nfr; kernel = kernel)

# ======================== C-mirror synthesize ========================

function synthesize_c!(S::AbstractMatrix,
                       theta_buf::AbstractVector,
                       BG::AbstractMatrix,
                       waves,
                       dt::Real;
                       kernel = kernel_gauss_c)
    Nb, Nfr = size(S)
    Nbg = size(BG, 2)
    Nw  = length(waves)
    @assert length(theta_buf) >= Nw

    @inbounds for k in 0:Nfr - 1
        bg_col = trunc(Int, (k / (Nfr - 1)) * (Nbg - 1))
        for i in 0:Nb - 1
            a = BG[i + 1, bg_col + 1]
            for w in 1:Nw
                Nt = waves[w].Nt
                A     = interpolate(Nfr, Nt, waves[w].A,     k)
                sigma = interpolate(Nfr, Nt, waves[w].sigma, k)

                if i == 0
                    if k == 0
                        theta_buf[w] = waves[w].theta0
                    else
                        v = interpolate(Nfr, Nt, waves[w].v, k - 1)
                        theta_buf[w] = range2pi(theta_buf[w] + v * dt)
                    end
                end

                dx = wrap(i * (L / Nb) - theta_buf[w])
                a += A * kernel(dx, sigma)
            end
            S[i + 1, k + 1] = a
        end
    end
    return S
end

function synthesize_c(data::Data; kernel = kernel_gauss_c)
    S = Matrix{Float64}(undef, data.Nb, data.Nfr)
    theta_buf = Vector{Float64}(undef, data.num_waves)
    synthesize_c!(S, theta_buf, data.BG, data.waves, data.dt; kernel = kernel)
    return S
end

# ‖S - XT‖₁ / ‖XT‖₁ — matches the C `synthesize`'s return value.
function residual_fraction(XT::AbstractMatrix, S::AbstractMatrix)
    T = promote_type(eltype(XT), eltype(S))
    diff   = zero(T)
    energy = zero(T)
    @inbounds for k in axes(XT, 2), i in axes(XT, 1)
        x = XT[i, k]
        diff   += abs(S[i, k] - x)
        energy += abs(x)
    end
    return diff / energy
end

# ======================== CSV / loader ========================

read_csv_matrix(path::AbstractString) = readdlm(path, ',', Float64)

function read_csv_vector(path::AbstractString)
    A = readdlm(path, ',', Float64)
    r, c = size(A)
    (r == 1 || c == 1) || error("$path is not a vector (got $(r) × $(c))")
    return vec(A)
end

function read_csv_scalar(path::AbstractString)
    v = read_csv_vector(path)
    length(v) == 1 || error("$path must contain exactly one value")
    return v[1]
end

function load_all_data(dir::AbstractString)
    XT = read_csv_matrix(joinpath(dir, "XT.csv"))
    BG = read_csv_matrix(joinpath(dir, "BG.csv"))
    Nb, Nfr = size(XT)
    size(BG, 1) == Nb || error("BG and XT row counts disagree ($(size(BG, 1)) vs $Nb)")
    Nbg = size(BG, 2)
    dt  = read_csv_scalar(joinpath(dir, "dt.csv"))

    waves = Wave{Float64}[]
    for i in 1:MAX_WAVES
        wdir = joinpath(dir, "wave_$i")
        isfile(joinpath(wdir, "A.csv")) || break

        A     = read_csv_vector(joinpath(wdir, "A.csv"))
        sigma = read_csv_vector(joinpath(wdir, "sigma.csv"))
        v     = read_csv_vector(joinpath(wdir, "v.csv"))
        theta0 = read_csv_scalar(joinpath(wdir, "theta0.csv"))

        Nt = length(A)
        length(sigma) == Nt ||
            error("Wave $i: A has $Nt values but sigma has $(length(sigma))")
        length(v) == Nt ||
            error("Wave $i: A has $Nt values but v has $(length(v))")

        push!(waves, Wave(A, sigma, v, Nt, theta0))
    end

    return Data(XT, BG, Nb, Nfr, Nbg, dt, waves, length(waves))
end
