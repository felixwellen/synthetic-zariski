# created using natural intelligence

plane = implicit_plot3d(
    lambda x, y, z: x ^2 + y^2+z^2-1,  # Equation x^2+y^2+z^2 = 1
    (-1.2, 1.2),             # x-range close to x=1 (to make it visible)
    (-2.7, 2.7),                # y-range
    (-2.7, 2.7),                # z-range
    color='lightblue',
    opacity=0.8
)
def L_x(t):
    return cos(t)
def L_y(t):
    return 0
def L_z(t):
    return -sin(t)

def L2_x(t):
    return 1/sqrt(2)*cos(t)
def L2_y(t):
    return 1/sqrt(2)*cos(t)
def L2_z(t):
    return -sin(t)

plane.show(aspect_ratio=1)
# Define axes with arrow tips
p1 = point3d((L_x(-0.8), L_y(-0.8), L_z(-0.8)), size=6, color='black')
p2 = point3d((L2_x(-1.1), L2_y(-1.1), L2_z(-1.1)), size=6, color='black')
q = point3d((L2_x(-pi*0.5), L2_y(-pi*0.5), L2_z(-pi*0.5)), size=6, color='black')

line1 = parametric_plot3d(
    [L_x,L_y,L_z],
    (t, -2.5, 1.0),
    color='red',
    thickness=4    
)


line2 = parametric_plot3d(
    [L2_x,L2_y,L2_z],
    (t, -2.5, 1.0),
    color='red',
    thickness=4    
)

scene = plane + q + p1 + p2 + line2 + line1
scene.show(aspect_ratio=1, frame=False)
