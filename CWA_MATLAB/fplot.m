function [ ] = fplot( leg, xlab, ylab, titl, ax, sz )

xlab.FontName = 'Times';
ylab.FontName = 'Times';
titl.FontName = 'Times';
ax.FontName = 'Times';

ax.FontSize = sz-6;
xlab.FontSize = sz;
ylab.FontSize = sz;
titl.FontSize = sz+2;

xlab.Interpreter = 'latex';
ylab.Interpreter = 'latex';
titl.Interpreter = 'latex';

if ~isempty(leg)
    leg.Interpreter = 'latex';
    leg.FontName = 'Times';
    leg.Box = 'off';
    leg.FontSize = sz-6;
end

set(gcf,'color','w')
set(gca,'box','off')


end

