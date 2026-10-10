"""Reproduce the explanatory GIF. Rounded coordinates are drawing data only.
The two sections have equal area since (sqrt(1-z*z))**2 = 1-z*z.
This illustration does not supply a curved-region volume definition.
Requires Pillow; run in this directory.
"""
from pathlib import Path
from math import sin, cos, pi, sqrt
from PIL import Image, ImageDraw, ImageFont
ROOT = Path(__file__).parent
W, H, SS = 960, 660, 2
BG = '#faf9f6'; INK = '#283c42'; GREEN = '#287b61'; BLUE = '#296da8'; ORANGE = '#b56932'; GRID = '#adb8ba'
FONT = '/System/Library/Fonts/Supplemental/Arial.ttf'
def font(n): return ImageFont.truetype(FONT, n*SS)
def frame(z):
    im=Image.new('RGB',(W*SS,H*SS),BG); d=ImageDraw.Draw(im)
    def line(points,color,width=2):d.line([(round(x*SS),round(y*SS)) for x,y in points],fill=color,width=width*SS)
    def text(x,y,s,n=19,color=INK):d.text((x*SS,y*SS),s,font=font(n),fill=color,anchor='mm')
    def poly(points,color):d.polygon([(round(x*SS),round(y*SS)) for x,y in points],fill=color)
    def ellipse(cx,cy,rx,ry,color,width=2,fill=None):
        d.ellipse(((cx-rx)*SS,(cy-ry)*SS,(cx+rx)*SS,(cy+ry)*SS),outline=color,width=width*SS,fill=fill)
    def ring(cx,r,height):return [(cx+132*r*cos(2*pi*i/160),245-120*height+37*r*sin(2*pi*i/160)) for i in range(161)]
    text(480,28,'Archimedes: compare the sections at the same height',25)
    text(240, 75,'Unit sphere',21);text(720,75,'Cylinder minus double cone',21)
    # Wireframe sphere: horizontal circles and meridians.
    for h in [-.8,-.4,0,.4,.8]:line(ring(240,sqrt(1-h*h),h),GRID,1)
    for angle in [0,pi/4,pi/2,3*pi/4]:
        line([(240+132*cos(a)*cos(angle),245-120*sin(a)+37*cos(a)*sin(angle)) for a in [2*pi*i/160 for i in range(161)]],GRID,1)
    # Cylinder and the two removed cones (common apex at the center).
    for x in [588,852]:line([(x,125),(x,365)],GRID)
    for h in [-1,1]:line(ring(720,1,h),GRID)
    for a in [0,pi/2,pi,3*pi/2]:
        for h in [-1,1]:line([(720,245),(720+132*cos(a),245-120*h+37*sin(a))],ORANGE,1)
    r=sqrt(1-z*z);yc=245-120*z
    line([(80,yc),(880,yc)],'#d8dee0',1)
    poly(ring(240,r,z), '#b6dccb');line(ring(240,r,z),GREEN,3)
    poly(ring(720,1,z),'#bdd6eb');poly(ring(720,abs(z),z),BG)
    line(ring(720,1,z),BLUE,3);line(ring(720,abs(z),z),ORANGE,2)
    text(480,403,'View the highlighted sections from above',19)
    ellipse(240,523,85,85,GREEN,2)
    ellipse(240,523,85*r,85*r,GREEN,3,'#b6dccb')
    ellipse(720,523,85,85,BLUE,3,'#bdd6eb')
    ellipse(720,523,85*abs(z),85*abs(z),ORANGE,2,BG)
    text(240,628,'Disk',19,GREEN);text(720,628,'Annulus: remove the cone section',19,BLUE)
    text(480,523,'Equal area',22)
    return im.resize((W,H),Image.Resampling.LANCZOS)
if __name__=='__main__':
    heights=[.98*cos(2*pi*i/72) for i in range(72)]
    frames=[frame(z) for z in heights]
    frames[10].save(ROOT/'archimedes-sections.png')
    frames[0].save(ROOT/'archimedes-sections.gif',save_all=True,append_images=frames[1:],duration=85,loop=0,optimize=True,disposal=2)
    with Image.open(ROOT/'archimedes-sections.gif') as gif:
        assert gif.n_frames==72 and gif.size==(W,H)
    print('Generated 72 frames, 6.12-second loop, plus still image.')
