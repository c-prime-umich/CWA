function [ t, thetap, XT, fps, Nb ] = XTReader_mod(XTStruct)
    
XT = XTStruct.XT;
t0 = XTStruct.t0;
fps = XTStruct.fps;

[ Nb, Nfr ] = size(XT);

dth = 2*pi/Nb;
thetap = 0:dth:2*pi-dth;

t = (0:Nfr-1)/fps + t0;

if nargout < 1
    
    figure
    set(gcf, 'Position', [200 200 2500 600])
    subplot('Position', [.1 .3 .8 .6])
    imagesc(t, thetap, XT)
    set(gca, 'Ydir', 'Normal')
    title(['Run ', num]);
    xlabel('Time [s]');
    ylabel('$\theta$');
    axis([ t(1) t(1)+300/fps 0 max(thetap)])
    formatPlot(gca,20)
    subplot('Position', [.1 .12 .8 .03])
    hold on
    imagesc(t,thetap, XT)
    plot([t(1) t(1)], [0 2*pi], 'r-', 'LineWidth', 3)
    plot([t(301) t(301)], [0 2*pi], 'r-', 'LineWidth', 3)
    hold off
    axis([t0(1) t(end) 0 max(thetap)])
    formatPlot(gca,20)
    set(gcf,'PaperPositionMode','auto')
    set(gca, 'YColor', 'none')
    set(gcf,'color','w');
    
end

end

