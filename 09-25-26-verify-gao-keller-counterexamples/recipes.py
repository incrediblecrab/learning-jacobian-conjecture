"""The paper's data, transcribed once: recipe inputs, claims, and where the printed displays live.

Source: Shuhong Gao, "Counterexamples to the Jacobian conjecture in dimensions greater than two", arXiv:2608.00222v1 (July 31, 2026), CC BY 4.0. Every gate reads this file (A, B and L); none defines paper data itself. One entry is ours, not the paper's, and is marked as such: G_COLLISION.

Conventions (paper Section 4.3, "the stage equations"):
  sweep       S_i(gamma, w) = X_i(w) + gamma * Delta_i(w),  i = 1..n-1, with det J_(gamma,w)(S) = c * gamma^k
  monomials   v_j = x^(m_j) * (source variable j+1)
  stage       (gamma, u_1..u_{n-2}) = polynomials in v  (constant Jacobian determinant det L)
  scalings    w_j = gamma^(d_j) * u_j
  twist       E_i = S_i(gamma, gamma^d u) / gamma^(e_i);  component i+1 = E_i(stage(v)) / x^(e_i);  component 1 = C = gamma * x
  claim       det J(F) = sign(order) * c * det L

Polynomial strings use Python syntax; "/" between integers is an exact rational.
"""

TEX = "source/Jacobian_CE.tex"
TEX_SHA256 = "c644040df10323c69de0b022986ee98563f659e70a53afd4a0c74c03d55d81aa"

MAPS = {
    "F": {
        "title": "Alpoge's map F (Section 3.4)",
        "params": ["w1"],
        "X": ["-3*w1**2 + 4*w1", "-w1**3 + w1**2"],  # (p(w), q(w))
        "Delta": ["2", "w1"],
        "c": 2, "k": 1, "d": [1], "e": [1, 2], "m": [1, 2],
        "source": ["x", "y", "z"],
        "stage": {"gamma": "2 - 3*v1 - v2", "u": ["1 + v1"]},
        "order": [2, 1, 0],  # paper lists (S_2/C^2, S_1/C, C): the reversal flips the sign
        "claims": {"degrees": [7, 6, 4], "det": "-2", "stage_det": "1", "generic_fiber": 3},
        "printed": [("f_1", None, "f_1 &=", ["f_2 &="]),
                    ("f_2", None, "f_2 &=", ["f_3 &="]),
                    ("f_3", None, "f_3 &=", ["\\end{align*}"])],
        # tangency cubic w^3 - 2w^2 + X w - 2Y with (X, Y) = (Y1, Y2), up to a constant factor
        "fiber": {"paper_R": "w1**3 - 2*w1**2 + Y1*w1 - 2*Y2", "targets": [
            {"name": "random target", "random": 1, "points": 3},
            {"name": "cusp preimage t=1 (curve C, empty fiber)", "paper_target": ["4/27", "4/3", "1"], "points": 0}]},
    },
    "G": {
        "title": "The degree-four map G (Section 3.5)",
        "params": ["w1"],
        "X": ["w1**3 - 6*w1**2 + 6*w1", "3/8*w1**4 - 2*w1**3 + 3/2*w1**2"],
        "Delta": ["2", "w1"],
        "c": 2, "k": 1, "d": [1], "e": [1, 2], "m": [1, 2],
        "source": ["x", "y", "z"],
        "stage": {"gamma": "2 - 4*v1 - v2", "u": ["1 + v1"]},
        "order": [0, 1, 2],
        "claims": {"degrees": [4, 11, 12], "det": "2", "stage_det": "1", "generic_fiber": 4},
        "printed": [("g_1", None, "g_1 ={}&", ["g_2 ={}&"]),
                    ("g_2", None, "g_2 ={}&", ["g_3 ={}&"]),
                    ("g_3", None, "g_3 ={}&", ["\\end{align*}"])],
        "fiber": {"paper_R": "1/4*w1**4 - 2*w1**3 + 3*w1**2 - Y1*w1 + 2*Y2", "targets": [
            {"name": "random target", "random": 2, "points": 4},
            {"name": "node (X,Y)=(-4,1/2) (empty fiber)", "Y": ["-4", "1/2"], "points": 0}]},
    },
    "F4": {
        "title": "F_4 (Section 4.4.1, Specialization I)",
        "params": ["w1", "w2"],
        "X": ["1/3*w1 - 4/3*w1**2 + w2*(w1**2 - 1)",
              "2/3*w1**2 - 8/9*w1**3 + w2*w1**3",
              "2*w1 + 7/9*w1**3 - 2/3*w1**4 + w2*(w1**4 + w1**2 + 2)"],
        "Delta": ["1", "w1", "w1**2"],
        "c": 2, "k": 1, "d": [1, 1], "e": [1, 2, 1], "m": [1, 1, 2],
        "source": ["x", "y", "z", "t"],
        "stage": {"gamma": "1 + v1 + v3", "u": ["1 + v2", "-7/9 + 22/9*v1 + 8/3*v2"]},
        "order": [0, 1, 2, 3],
        "claims": {"degrees": [4, 11, 12, 21], "det": "-44/9", "stage_det": "-22/9", "generic_fiber": 5},
        "printed": [("F_{4,1}", None, "F_{4,1} ={}&", ["F_{4,2} ={}&"]),
                    ("F_{4,2}", None, "F_{4,2} ={}&", ["F_{4,3} ={}&"]),
                    ("F_{4,3}", None, "F_{4,3} ={}&", ["F_{4,4} ={}&"]),
                    ("F_{4,4}", None, "F_{4,4} ={}&", ["\\end{align*}"])],
        "fiber": {"paper_R": "2/9*w1**5 + 2/9*w1**4 + (8/9 + Y1)*w1**3 - (4/3 + 2*Y2)*w1**2 + (2*Y1 + Y3)*w1 - 2*Y2",
                  "targets": [{"name": "paper witness v=(2/3,-1/5,1/2,3)", "paper_target": ["2/3", "-1/5", "1/2", "3"], "points": 5},
                              {"name": "random target", "random": 3, "points": 5}]},
    },
    "F5": {
        "title": "F_5 (Section 4.4.2, Specialization II)",
        "params": ["w1", "w2"],
        "X": ["160/29*w1**3 - 60/29*w1**2 - 240/29*w1*w2 + 51/29*w1 + 60/29*w2",
              "60/29*w1**4 - 20/29*w1**3 - 120/29*w2**2 + 51/29*w2",
              "-48/29*w1**5 + 15/29*w1**4 + 240/29*w1**3*w2 - 17/29*w1**3 - 60/29*w1**2*w2 - 240/29*w1*w2**2 + 51/29*w1*w2 + 30/29*w2**2"],
        "X_printed": [("X_1", "\\label{subsec:specII}", "X_1&=", ["X_2&="]),
                      ("X_2", "\\label{subsec:specII}", "X_2&=", ["X_3&="]),
                      ("X_3", "\\label{subsec:specII}", "X_3&=", ["\\end{align*}"])],
        "Delta": ["1", "w1", "w2"],
        "c": 1, "k": 2, "d": [1, 2], "e": [1, 2, 3], "m": [1, 2, 3],
        "source": ["x", "y", "z", "t"],
        "stage": {"gamma": "1 + 20/29*v1", "u": ["1 - 49/29*v1 + 8*v2", "1 - 69/29*v1 + 9*v2 + v3 + 4197/1682*v1**2"]},
        "order": [0, 1, 2, 3],
        "claims": {"degrees": [3, 12, 14, 16], "det": "160/29", "stage_det": "160/29", "generic_fiber": 10},
        "printed": [("F_{5,1}", None, "F_{5,1} ={}&", ["F_{5,2} ={}&"]),
                    ("F_{5,2}", None, "F_{5,2} ={}&", ["F_{5,3} ={}&"]),
                    ("F_{5,3}", None, "F_{5,3} ={}&", ["F_{5,4} ={}&"]),
                    ("F_{5,4}", None, "F_{5,4} ={}&", ["\\end{align*}"])],
        "fiber": {"paper_R_tex": ("R(w_1;Y)", "\\label{thm:F5}", "R(w_1;Y)={}&", ["\\end{align*}"]),
                  "targets": [{"name": "paper witness v=(1/2,2/3,-1/3,1)", "paper_target": ["1/2", "2/3", "-1/3", "1"], "points": 10},
                              {"name": "random target", "random": 4, "points": 10}]},
    },
    "F6": {
        "title": "F_6 (Section 4.5.1, bottom branch)",
        "params": ["w1", "w2", "w3"],
        "defs": [("G2", "w2 + w1*w3 + w1**2 - w1**3"),
                 ("G3", "2*w1*G2 + w2"),
                 ("G4", "w3 - G2**2 + 2*w1**4 - 2*w1**5")],
        "potentials": ["G2", "G3", "G4"],  # X_1 = -det J_w(G2,G3,G4)/c, X_{i+1} = G_{i+1} + Delta_{i+1} X_1
        "X_printed": [("X_1", "\\label{subsubsec:bottom5}", "X_1&=", ["X_2&="]),
                      ("X_2", "\\label{subsubsec:bottom5}", "X_2&=", ["X_3&="]),
                      ("X_3", "\\label{subsubsec:bottom5}", "X_3&=", ["X_4&="]),
                      ("X_4", "\\label{subsubsec:bottom5}", "X_4&=", ["\\end{align*}"])],
        "Delta": ["1", "w1", "w1**2", "w2"],
        "c": 1, "k": 1, "d": [1, 3, 4], "e": [1, 2, 3, 4], "m": [1, 2, 3, 4],
        "source": ["x", "y", "z1", "z2", "z3"],
        "stage": {"gamma": "1 - 29*v1 + 999*v1**2 + 355*v1*v2 - 41553*v1**3 + v4",
                  "u": ["1 + 27*v1 - 5*v2", "v1 - 12*v2 + 2128/5*v1**2 + v3", "-4*v1 - 10*v2"]},
        "order": [0, 1, 2, 3, 4],
        "base": ["1", "1", "0", "0"],
        "gradients": [[-16, -17, 3, 2], [-17, -18, 5, 3], [-2, -2, 0, 1]],  # grad E_2, E_3, E_4 at the base point
        "claims": {"degrees": [7, 38, 40, 42, 44], "det": "-290", "stage_det": "-290", "generic_fiber": 6,
                   "terms": [6, 342, 421, 507, 904]},
        "printed": [("F_{6,1}", None, "F_{6,1}\\;=\\;", ["\\]"])],
        "fiber": {"paper_R": "2*w1**6 - 2*w1**5 - w1**3 + (Y1 + 1)*w1**2 + (Y4 + Y2**2 - Y1*Y3 - 2*Y2 + Y1)*w1 + (Y3 - Y2)",
                  "targets": [{"name": "random target", "random": 5, "points": 6},
                              {"name": "axis (C0,0,0,0,0)", "paper_target": ["1", "0", "0", "0", "0"], "points": 4,
                               "paper_R0": "w1**2*(w1 - 1)*(2*w1**3 - 1)"}]},
    },
    "F7": {
        "title": "F_7 (Section 4.6, curve-type family)",
        "params": ["w1", "w2", "w3"],
        "defs": [("H3", "w2 + w1**3 + w1**2*w3"),
                 ("H4", "w3 + w1**4"),
                 ("G2", "w2**2 + w2 + w1*w3 + w1**3"),
                 ("G3", "2*w1*G2 + H3"),
                 ("G4", "3*w1**2*G2 + H4")],
        "potentials": ["G2", "G3", "G4"],
        "Delta": ["1", "w1", "w1**2", "w1**3"],
        "c": 1, "k": 1, "d": [1, 3, 4], "e": [1, 2, 3, 4], "m": [1, 2, 3, 4],
        "source": ["x", "y", "z1", "z2", "z3"],
        "stage": {"gamma": "1 - 61*v1 + 9012*v1**2 + 238/19*v1*v2 - 35823670/19*v1**3 + 8*v3 + v4",
                  "u": ["1 + 59*v1 + v2 - 5178*v1**2 + 19*v3", "-7*v1 - 27*v2", "-1 - 234*v1 - 5*v2"]},
        "order": [0, 1, 2, 3, 4],
        "base": ["1", "1", "0", "-1"],
        "gradients": [[-15, 0, -3, 4], [-20, 3, -1, 6], [-19, 8, -1, 7]],
        "claims": {"degrees": [7, 86, 89, 92, 95], "det": "119377", "stage_det": "119377", "generic_fiber": 12,
                   "terms": [7, None, None, None, None], "term_range": [14000, 26000]},
        "printed": [("F_{7,1}", None, "F_{7,1}\\;=\\;", ["\\]"])],
        "fiber": {"paper_R": "p1**2 + p1 + w1*p2 + w1**3 + Y1*w1 - Y2",
                  "paper_R_defs": [("p2", "Y4 - 3*Y2*w1**2 + 2*Y1*w1**3 - w1**4"),
                                   ("p1", "Y3 - 2*Y2*w1 + Y1*w1**2 - w1**3 - w1**2*p2")],
                  "targets": [{"name": "paper witness Y=(1,2,-1,3)", "Y": ["1", "2", "-1", "3"], "points": 12},
                              {"name": "axis (C0,0,0,0,0)", "paper_target": ["1", "0", "0", "0", "0"], "points": 7,
                               "paper_R0": "w1**5*(w1 - 1)*(w1**6 + w1**5 + w1**4 - w1**3 - w1**2 - w1 + 1)"}]},
    },
}

# Alpoge's map: three rational points with one image (Section 3.4).
F_COLLISION = {"points": [["0", "0", "-1/4"], ["1", "-3/2", "13/2"], ["-1", "3/2", "13/2"]],
               "image": ["-1/4", "0", "0"]}

# Not printed in the paper: an explicit rational three-point fiber of G. It is the target v = (0, 1, 0) in the v_1 = 0 case of the paper's Theorem A.1 (Fiber sizes of G), which gives one point (0, v_2/2, z*) on x = 0 and two points on gamma = 0 with x^2 = 4/(v_2^2 - 24 v_3). Here x^2 = 4, so all three points are rational. The target was chosen for its small numbers.
G_COLLISION = {"points": [["0", "1/2", "-9/4"], ["2", "-1/2", "3/2"], ["-2", "5/6", "13/6"]],
               "image": ["0", "1", "0"]}

# Theorem 3.4 of the paper, in the target coordinates v = (v1, v2, v3) of F.
F_THM34 = {"c3": "27*v1**2*v3**2 - 18*v1*v2*v3 + 16*v1 + v2**3*v3 - v2**2",
           "a2": "54*v1*v3**2 - 18*v2*v3 + 16",
           "E": "X**3 - X**2 - 18*X*Y + 16*Y + 27*Y**2",
           "sigma": ["v2*v3", "v1*v3**2"]}

# Appendix A.1: the six-element lex Groebner basis of the graph ideal of F, order z > y > x > v1 > v2 > v3.
F_GB = [("h_%d" % i, "\\label{app:F}", "h_%d ={}&" % i, ["h_%d ={}&" % (i + 1)] if i < 6 else ["\\end{align*}"])
        for i in range(1, 7)]

# Appendix A.2: G's tangency quartic, curve equation and reconstruction formulas.
G_APPENDIX = {"W": "1/4*w**4 - 2*w**3 + 3*w**2 - X*w + 2*Y",
              "p": "w**3 - 6*w**2 + 6*w",
              "E": "27*X**4 + 80*X**3 - 672*X**2*Y + 1536*X*Y**2 - 512*Y**3 - 144*X**2 - 2304*X*Y + 4608*Y**2 + 3456*Y",
              "node": ["-4", "1/2"], "node_square": "1/4*(w**2 - 4*w - 2)**2",
              "point_over_011": {"point": ["0", "1/2", "-1/4"], "image": ["0", "1", "1"]}}
