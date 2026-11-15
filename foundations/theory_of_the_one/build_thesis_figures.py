#!/usr/bin/env python3
"""Modern thesis illustrations; integer data, floating-point display geometry only."""
from __future__ import annotations

import json
from math import gcd, lcm
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle, Circle, FancyArrowPatch


OUT = Path(__file__).resolve().parent / 'figures'
OUT.mkdir(parents=True, exist_ok=True)
INK = '#20343C'
TEAL = '#247C80'
COPPER = '#A85F35'
PALE_TEAL = '#E9F3F1'
PALE_COPPER = '#FAEFE7'
PALE_GRAY = '#F0F2F2'
GRAY = '#A4B0B3'
LINE = '#B7C5C8'
WHITE = '#FFFFFF'

plt.rcParams.update({
    'font.family': 'DejaVu Sans',
    'font.size': 11,
    'text.color': INK,
    'axes.labelcolor': INK,
    'axes.edgecolor': LINE,
    'xtick.color': INK,
    'ytick.color': INK,
    'svg.fonttype': 'none',
    'figure.facecolor': WHITE,
    'savefig.facecolor': WHITE,
    'mathtext.fontset': 'dejavusans',
})

META = {'provenance': 'Modern explanatory illustrations created for Theory of the One; not ancient diagrams.',
        'calculation_policy': 'All counts, residues, quotients, and capacities are exact integers. Noninteger values occur only in display geometry.',
        'figures': {}, 'euclid_definitions': {}}


def save(fig, name):
    fig.savefig(OUT / (name + '.png'), dpi=300, bbox_inches='tight', pad_inches=0.12)
    fig.savefig(OUT / (name + '.svg'), bbox_inches='tight', pad_inches=0.12)
    plt.close(fig)


def compatible_grid():
    fig, axes = plt.subplots(1, 2, figsize=(9.0, 6.9))
    fig.subplots_adjust(left=0.08, right=0.97, bottom=0.26, top=0.82, wspace=0.34)
    fig.suptitle('The orbit of one and compatible residue states', fontsize=17, y=0.96, fontweight='medium')
    panels = []
    for ax, (m, n) in zip(axes, [(3, 5), (6, 10)]):
        period = lcm(m, n)
        orbit = {(k % m, k % n): k for k in range(period)}
        for y in range(n):
            for x in range(m):
                admitted = (x, y) in orbit
                cell = Rectangle((x - 0.5, y - 0.5), 1, 1,
                                 facecolor=PALE_TEAL if admitted else PALE_GRAY,
                                 edgecolor=LINE, linewidth=0.7,
                                 hatch=None if admitted else '///')
                ax.add_patch(cell)
                if admitted:
                    ax.text(x, y, str(orbit[x, y]), ha='center', va='center',
                            fontsize=13 if m == 3 else 10.7,
                            color=INK, fontweight='medium')
        ax.add_patch(Rectangle((-0.5, -0.5), 1, 1, fill=False, edgecolor=COPPER, linewidth=2.0))
        ax.set_xlim(-0.5, m - 0.5)
        ax.set_ylim(-0.5, n - 0.5)
        ax.set_aspect('equal')
        ax.set_xticks(range(m))
        ax.set_yticks(range(n))
        ax.tick_params(length=0, pad=7)
        ax.set_xlabel('Residue modulo ' + str(m), labelpad=9)
        ax.set_ylabel('Residue modulo ' + str(n), labelpad=9)
        ax.set_title('Moduli ' + str(m) + ' and ' + str(n) + '\n' + str(period) + ' compatible states of ' + str(m * n),
                     fontsize=13, pad=15, fontweight='medium')
        for spine in ax.spines.values():
            spine.set_visible(False)
        panels.append({'moduli': [m, n], 'gcd': gcd(m, n), 'product_cells': m * n,
                       'lcm_period': period, 'compatible_cells_drawn': len(orbit),
                       'incompatible_cells_drawn': m * n - len(orbit),
                       'canonical_integer_labels': sorted(orbit.values())})
    fig.text(0.5, 0.105, 'Cell labels give n in the orbit n · (1, 1), from 0 to period − 1.',
             ha='center', fontsize=11)
    fig.text(0.5, 0.064, 'Teal cells are compatible; hatched cells violate agreement on the shared factor.',
             ha='center', fontsize=10.5)
    fig.text(0.5, 0.024, 'For 6 and 10, the two residues must have equal parity. Capacity is lcm, not the raw product.',
             ha='center', fontsize=10.2)
    META['figures']['compatible_residue_grids'] = {'panels': panels}
    save(fig, 'compatible_residue_grids')


def phase_recovery():
    M, A, x, q = 36, 37, 1001, 11
    r, s = x % M, x % A
    K = (r - s) % A
    reduced = [r % q, M % q, K % q]
    target = (reduced[0] + reduced[1] * reduced[2]) % q
    assert (r, s, K, target) == (29, 2, 27, 0)
    assert 0 <= x < M * A and x == r + M * K
    fig, ax = plt.subplots(figsize=(9.4, 6.3))
    fig.subplots_adjust(left=0.035, right=0.965, top=0.88, bottom=0.06)
    ax.set_xlim(0, 12)
    ax.set_ylim(0, 8)
    ax.axis('off')
    fig.suptitle('Phase recovery from the consecutive pair 36 and 37',
                 fontsize=16, y=0.97, fontweight='medium')
    ax.text(6, 7.6, 'Worked value x = 1001     |     admitted range 0 ≤ x < 36 · 37 = 1332',
            ha='center', va='center', fontsize=12)
    ax.text(6, 7.25, r'Write $x=r_{36}+36K$, with $0\leq r_{36}<36$.',
            ha='center', va='center', fontsize=11.2)
    # Two authentic observations. Their frames distinguish observations from the derived result.
    for left, title, equation in [(0.3, 'Shell observation', r'$r_{36}=1001\;\mathrm{mod}\;36=29$'),
                                  (6.5, 'Anchor observation', r'$r_{37}=1001\;\mathrm{mod}\;37=2$')]:
        ax.add_patch(Rectangle((left, 5.82), 5.2, 1.22, facecolor=PALE_TEAL,
                               edgecolor=TEAL, linewidth=1.1))
        ax.text(left + 2.6, 6.72, title, ha='center', fontsize=11.2, fontweight='medium')
        ax.text(left + 2.6, 6.15, equation, ha='center', fontsize=14)
    for source in [(2.9, 5.8), (9.1, 5.8)]:
        ax.add_patch(FancyArrowPatch(source, (6, 5.40), arrowstyle='-|>', mutation_scale=13,
                                    linewidth=1.2, color=TEAL, connectionstyle='arc3,rad=0'))
    ax.text(6, 5.0, r'$36\equiv-1\;(\mathrm{mod}\;37)\quad\Longrightarrow\quad K\equiv r_{36}-r_{37}\;(\mathrm{mod}\;37)$',
            ha='center', fontsize=13.5)
    ax.text(6, 4.25, r'$K=(29-2)\;\mathrm{mod}\;37=27$', ha='center', fontsize=18, color=INK)
    ax.text(6, 3.68, 'The admitted range gives 0 ≤ K < 37, selecting K = 27 exactly.',
            ha='center', fontsize=11.5)
    ax.add_patch(FancyArrowPatch((6, 3.35), (6, 2.98), arrowstyle='-|>', mutation_scale=13,
                                linewidth=1.2, color=TEAL))
    ax.add_patch(Rectangle((0.7, 1.2), 10.6, 1.65, facecolor=PALE_COPPER,
                           edgecolor=COPPER, linewidth=1.1))
    ax.text(6, 2.53, 'Direct output modulo 11', ha='center', fontsize=11.7, fontweight='medium')
    ax.text(6, 1.95, r'$x\;\mathrm{mod}\;11=[(29\;\mathrm{mod}\;11)+(36\;\mathrm{mod}\;11)(27\;\mathrm{mod}\;11)]\;\mathrm{mod}\;11$',
            ha='center', fontsize=12.8)
    ax.text(6, 1.43, r'$=(7+3\cdot5)\;\mathrm{mod}\;11=22\;\mathrm{mod}\;11=0$', ha='center', fontsize=14.5)
    ax.text(6, 0.65, 'Identity check: 29 + 36 · 27 = 1001. The winding is derived from the two phases.',
            ha='center', fontsize=11.2)
    ax.text(6, 0.12, 'Both observations must refer to the same source value and operation.',
            ha='center', fontsize=10.5)
    META['figures']['phase_recovery_36_37'] = {
        'M': M, 'A': A, 'source_x': x, 'source_range_lower': 0,
        'source_range_upper_exclusive': M * A, 'r_M': r, 'r_A': s, 'derived_K': K,
        'target_modulus': q, 'target_reduced_operands': reduced,
        'target_integer_sum_before_mod': reduced[0] + reduced[1] * reduced[2],
        'target_residue': target, 'identity_check': r + M * K == x}
    save(fig, 'phase_recovery_36_37')


class PlatePanel:
    def __init__(self, ax, number, title):
        self.ax, self.number = ax, number
        self.units = []
        self.groups = []
        ax.set_xlim(0, 12)
        ax.set_ylim(0, 8.5)
        ax.set_aspect('equal')
        ax.axis('off')
        ax.text(0.05, 8.2, str(number) + '  ' + title, fontsize=13.6,
                fontweight='medium', ha='left', va='top')

    def circle(self, x, y, group_id, role='main'):
        color = TEAL if role == 'main' else COPPER if role == 'remainder' else GRAY
        self.ax.add_patch(Circle((x, y), radius=0.19, facecolor=color,
                                 edgecolor=INK, linewidth=0.45, zorder=3))
        self.units.append({'group': group_id, 'role': role})

    def group(self, n, cx, cy, group_id, cols=None, label=None, role='main', hatch=False):
        if cols is None:
            cols = min(n, 3)
        rows = (n + cols - 1) // cols
        pitch = 0.68
        width, height = cols * pitch, rows * pitch
        left, bottom = cx - width / 2, cy - height / 2
        face = PALE_TEAL if role == 'main' else PALE_COPPER if role == 'remainder' else PALE_GRAY
        edge = TEAL if role == 'main' else COPPER if role == 'remainder' else GRAY
        self.ax.add_patch(Rectangle((left - 0.12, bottom - 0.12), width + 0.24, height + 0.24,
                                   facecolor=face, edgecolor=edge, linewidth=0.9,
                                   hatch='///' if hatch else None, zorder=0))
        for i in range(n):
            self.circle(left + ((i % cols) + 0.5) * pitch,
                        bottom + (rows - (i // cols) - 0.5) * pitch, group_id, role)
        if label is not None:
            self.ax.text(cx, bottom - 0.62, str(label), ha='center', va='center', fontsize=11.8)
        self.groups.append({'id': group_id, 'units': n, 'rows': rows, 'columns': cols, 'role': role})
        return left, bottom, width, height

    def array(self, rows, cols, cx, cy, group_id, pitch=0.75, side_labels=False):
        width, height = cols * pitch, rows * pitch
        left, bottom = cx - width / 2, cy - height / 2
        self.ax.add_patch(Rectangle((left, bottom), width, height, facecolor=PALE_TEAL,
                                   edgecolor=TEAL, linewidth=1.0, zorder=0))
        for c in range(1, cols):
            self.ax.plot([left + c * pitch] * 2, [bottom, bottom + height], color=LINE, linewidth=0.5, zorder=1)
        for r in range(1, rows):
            self.ax.plot([left, left + width], [bottom + r * pitch] * 2, color=LINE, linewidth=0.5, zorder=1)
        for r in range(rows):
            for c in range(cols):
                self.circle(left + (c + 0.5) * pitch, bottom + (r + 0.5) * pitch, group_id)
        if side_labels:
            self.bracket(left, left + width, bottom - 0.28, str(cols))
            self.ax.plot([left - 0.24, left - 0.38, left - 0.38, left - 0.24],
                         [bottom, bottom, bottom + height, bottom + height], color=INK, linewidth=0.9)
            self.ax.text(left - 0.69, cy, str(rows), ha='center', va='center', fontsize=11.8)
        self.groups.append({'id': group_id, 'units': rows * cols, 'rows': rows, 'columns': cols, 'role': 'main'})
        return left, bottom, width, height

    def bracket(self, x1, x2, y, label):
        self.ax.plot([x1, x1, x2, x2], [y + 0.17, y, y, y + 0.17], color=INK, linewidth=0.9)
        self.ax.text((x1 + x2) / 2, y - 0.52, label, ha='center', va='center', fontsize=11.5)

    def note(self, text, y=1.45):
        self.ax.text(6, y, text, ha='center', va='center', fontsize=11.4)

    def plus(self, x, y=4.6):
        self.ax.text(x, y, '+', ha='center', va='center', fontsize=17)

    def finish(self, expected):
        assert len(self.units) == expected, (self.number, len(self.units), expected)
        META['euclid_definitions'][str(self.number)] = {
            'unit_circles_drawn': len(self.units), 'expected_units_in_display': expected,
            'count_verified': len(self.units) == expected,
            'groups': self.groups,
            'highlighted_units': sum(u['role'] == 'main' for u in self.units),
            'remainder_units': sum(u['role'] == 'remainder' for u in self.units)}


TITLES = {
 1:'Unit', 2:'Number', 3:'Part', 4:'Parts', 5:'Multiple', 6:'Even', 7:'Odd',
 8:'Even-times-even', 9:'Even-times-odd', 10:'Odd-times-odd', 11:'Prime',
 12:'Relatively prime', 13:'Composite', 14:'Relatively composite', 15:'Multiplication',
 16:'Plane number', 17:'Solid number', 18:'Square', 19:'Cube', 20:'Proportional numbers',
 21:'Similar plane numbers', 22:'Perfect number'}
EXPECTED = {1:1,2:6,3:12,4:9,5:12,6:6,7:7,8:12,9:12,10:9,11:7,12:17,13:8,
            14:16,15:12,16:12,17:24,18:9,19:27,20:15,21:30,22:6}


def draw_definition(ax, n):
    p = PlatePanel(ax, n, TITLES[n])
    if n == 1:
        p.group(1,6,4.8,'unit',label='1')
        p.note('One thing counted as one unit.')
    elif n == 2:
        p.group(6,6,4.8,'number',cols=6,label='6 units')
        p.note('A multitude composed of units.')
    elif n in (3,5):
        for j,cx in enumerate([1.65,4.55,7.45,10.35]):
            p.group(3,cx,4.8,'measure_'+str(j+1),cols=3,label='3',
                    role='main' if n==5 or j==0 else 'context')
        p.note('3 measures 12 exactly, four times.' if n==3 else '12 contains four equal copies of 3.')
    elif n == 4:
        for j,cx in enumerate([2.0,6.0,10.0]):
            p.group(3,cx,5.0,'third_'+str(j+1),cols=3,label='3',
                    role='main' if j<2 else 'context',hatch=j<2)
        p.bracket(0.86,7.14,3.65,'Selected 6')
        p.note('6 of 9: two of its three equal parts.',y=1.35)
        p.note('6 does not measure 9.',y=0.62)
    elif n == 6:
        for j,cx in enumerate([3.0,9.0]): p.group(3,cx,4.8,'half_'+str(j+1),cols=3,label='3')
        p.plus(6,4.8)
        p.note('6 splits into two equal parts.')
    elif n == 7:
        for j,cx in enumerate([2.2,6.0]): p.group(3,cx,4.8,'part_'+str(j+1),cols=3,label='3')
        p.group(1,10.0,4.8,'unpaired',label='1 unpaired',role='remainder',hatch=True)
        p.plus(4.1,4.8);p.plus(8.0,4.8)
        p.note('7 leaves one unit after equal pairing.')
    elif n == 8:
        for j,cx in enumerate([3.0,9.0]): p.group(6,cx,4.8,'copy_'+str(j+1),cols=3,label='6')
        p.note('12: an even measure 6, repeated 2 times.')
    elif n == 9:
        for j,cx in enumerate([2.0,6.0,10.0]): p.group(4,cx,4.8,'copy_'+str(j+1),cols=2,label='4')
        p.note('12: an even measure 4, repeated 3 times.')
    elif n == 10:
        for j,cx in enumerate([2.0,6.0,10.0]): p.group(3,cx,4.8,'copy_'+str(j+1),cols=3,label='3')
        p.note('9: an odd measure 3, repeated 3 times.')
    elif n == 11:
        for j in range(7): p.group(1,2.4+j*1.2,4.8,'unit_'+str(j+1),label='1')
        p.note('7 has only 1 as a smaller exact measure.')
    elif n == 12:
        ax.text(0.35,6.1,'8',ha='left',va='center',fontsize=12.5)
        for j,cx in enumerate([4.0,8.0]):p.group(4,cx,6.1,'eight_part_'+str(j+1),cols=4)
        ax.text(0.35,3.8,'9',ha='left',va='center',fontsize=12.5)
        for j,cx in enumerate([2.7,6.0,9.3]):p.group(3,cx,3.8,'nine_part_'+str(j+1),cols=3)
        p.note('8 and 9 have only the common measure 1.')
    elif n == 13:
        for j,cx in enumerate([3.0,9.0]):p.group(4,cx,4.8,'factor_'+str(j+1),cols=2,label='4')
        p.note('4 measures 8 exactly.')
    elif n == 14:
        ax.text(6,7.1,'6 units',ha='center',fontsize=11.5)
        for j,cx in enumerate([3.0,6.0,9.0]):p.group(2,cx,6.0,'six_pair_'+str(j+1),cols=2,label='2')
        ax.text(6,4.5,'10 units',ha='center',fontsize=11.5)
        for j,cx in enumerate([1.35,3.675,6.0,8.325,10.65]):p.group(2,cx,3.4,'ten_pair_'+str(j+1),cols=2,label='2')
        p.note('The number 2 measures both 6 and 10.',y=1.2)
    elif n == 15:
        for j,cx in enumerate([2.0,6.0,10.0]):p.group(4,cx,4.8,'summand_'+str(j+1),cols=2,label='4')
        p.plus(4,4.8);p.plus(8,4.8)
        p.note('Take 4 three times: 4 + 4 + 4 = 12.')
    elif n == 16:
        p.array(3,4,6,4.7,'plane',pitch=0.9,side_labels=True)
        p.note('Sides 3 and 4 contain 12 units.',y=1.25)
    elif n == 17:
        for j,cx in enumerate([3.0,9.0]):
            ax.text(cx,6.6,'Layer '+str(j+1),ha='center',fontsize=11.5)
            p.array(3,4,cx,4.7,'layer_'+str(j+1),pitch=0.72)
            ax.text(cx,3.05,'3 rows · 4 columns',ha='center',fontsize=10.8)
        p.note('2 layers of 3 by 4: 24 units.',y=1.4)
    elif n == 18:
        p.array(3,3,6,4.7,'square',pitch=0.9,side_labels=True)
        p.note('Two equal sides: 3 by 3 gives 9.',y=1.25)
    elif n == 19:
        for j,cx in enumerate([2.0,6.0,10.0]):
            ax.text(cx,6.4,'Layer '+str(j+1),ha='center',fontsize=11.4)
            p.array(3,3,cx,4.7,'layer_'+str(j+1),pitch=0.68)
            ax.text(cx,3.1,'9 units',ha='center',fontsize=11.1)
        p.note('Three equal factors: 3 · 3 · 3 = 27.',y=1.4)
    elif n == 20:
        for count,cx,cy,name in [(2,3,6.1,'first'),(3,3,3.7,'second'),(4,9,6.1,'third'),(6,9,3.7,'fourth')]:
            p.group(count,cx,cy,name,cols=count,label=str(count))
        p.note('2 : 3 = 4 : 6; both ratios are two thirds.',y=1.25)
    elif n == 21:
        for rows,cols,cx,name in [(2,3,3,'small_plane'),(4,6,9,'large_plane')]:
            pitch=0.63
            p.array(rows,cols,cx,3.25+rows*pitch/2,name,pitch=pitch,side_labels=True)
            ax.text(cx,6.7,str(rows)+' by '+str(cols)+' = '+str(rows*cols),ha='center',fontsize=12)
        p.note('Corresponding sides: 2 : 4 = 3 : 6.',y=1.4)
    elif n == 22:
        for j,(count,cx) in enumerate([(1,2.0),(2,6.0),(3,10.0)]):
            p.group(count,cx,4.8,'proper_divisor_'+str(count),cols=count,label=str(count))
        p.plus(4,4.8);p.plus(8,4.8)
        p.note('All proper parts together: 1 + 2 + 3 = 6.')
    p.finish(EXPECTED[n])


def euclid_plates():
    for plate in range(6):
        start=plate*4+1
        end=min(22,start+3)
        numbers=list(range(start,end+1))
        rows=2 if len(numbers)>2 else 1
        fig, axes=plt.subplots(rows,2,figsize=(9.2,7.65 if rows==2 else 4.3),squeeze=False)
        fig.subplots_adjust(left=0.035,right=0.975,bottom=0.08 if rows==2 else 0.14,
                            top=0.9 if rows==2 else 0.82,wspace=0.12,hspace=0.16)
        fig.suptitle('Euclid, Book VII · Definitions '+str(start)+'–'+str(end),
                     fontsize=16.5,y=0.97,fontweight='medium')
        for ax,n in zip(axes.flatten(),numbers):draw_definition(ax,n)
        fig.text(0.5,0.027 if rows==2 else 0.035,
                 'Modern counted illustrations · one circle = one unit · group boundaries are explicit',
                 ha='center',fontsize=10.2)
        name='euclid_plate_'+str(plate+1).zfill(2)
        META['figures'][name]={'definitions':numbers,
                               'unit_circles_drawn':sum(EXPECTED[n] for n in numbers),
                               'numbering_preserved':True}
        save(fig,name)


def main():
    compatible_grid()
    phase_recovery()
    euclid_plates()
    assert len(META['euclid_definitions'])==22
    assert all(item['count_verified'] for item in META['euclid_definitions'].values())
    META['all_euclid_counts_verified']=True
    META['definitions_numbered']=list(range(1,23))
    META['total_unit_circles_across_euclid_plates']=sum(EXPECTED.values())
    (OUT/'figure_checks.json').write_text(json.dumps(META,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'figures':len(META['figures']), 'png_files':len(list(OUT.glob('*.png'))),
                      'svg_files':len(list(OUT.glob('*.svg'))), 'definitions':22,
                      'unit_circles':META['total_unit_circles_across_euclid_plates'],
                      'counts_verified':True},indent=2))


if __name__=='__main__':main()
