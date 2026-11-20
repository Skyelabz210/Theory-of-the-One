from pathlib import Path
import os
import subprocess
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import ListedColormap
from docx import Document
from docx.shared import Inches, Pt, RGBColor
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.enum.table import WD_TABLE_ALIGNMENT, WD_CELL_VERTICAL_ALIGNMENT
from docx.oxml import OxmlElement
from docx.oxml.ns import qn

ROOT = Path(__file__).resolve().parent
FONT = 'Liberation Serif'
SANS = 'Liberation Sans'
MATH = 'Latin Modern Math'
DOCX = ROOT / 'Arbitrary_Moduli_in_CRAM.docx'


def set_font(style, family, size, bold=False):
    style.font.name = family
    style.font.size = Pt(size)
    style.font.bold = bold
    style.font.color.rgb = RGBColor(0, 0, 0)
    rpr = style.element.get_or_add_rPr()
    rf = rpr.find(qn('w:rFonts'))
    if rf is None:
        rf = OxmlElement('w:rFonts')
        rpr.insert(0, rf)
    for field in ('ascii', 'hAnsi', 'cs', 'eastAsia'):
        rf.set(qn('w:' + field), family)
    for field in ('asciiTheme', 'hAnsiTheme', 'cstheme', 'eastAsiaTheme'):
        rf.attrib.pop(qn('w:' + field), None)


def set_cell_shading(cell, fill):
    pr = cell._tc.get_or_add_tcPr()
    for old in pr.findall(qn('w:shd')):
        pr.remove(old)
    shd = OxmlElement('w:shd')
    shd.set(qn('w:fill'), fill)
    shd.set(qn('w:val'), 'clear')
    pr.append(shd)


def figure():
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10})
    fig, axes = plt.subplots(1, 2, figsize=(8.6, 3.35), constrained_layout=True)
    palette = ListedColormap(['#eef0f2', '#294e67'])
    for ax, (m, a) in zip(axes, [(5, 7), (6, 10)]):
        valid = np.zeros((a, m), dtype=int)
        for x in range(int(np.lcm(m, a))):
            valid[x % a, x % m] = 1
        ax.imshow(valid, cmap=palette, vmin=0, vmax=1, origin='lower', aspect='equal')
        ax.set_xticks(range(m))
        ax.set_yticks(range(a))
        ax.set_xticks(np.arange(-.5, m, 1), minor=True)
        ax.set_yticks(np.arange(-.5, a, 1), minor=True)
        ax.grid(which='minor', color='white', linewidth=1.3)
        ax.tick_params(which='minor', bottom=False, left=False)
        ax.tick_params(which='major', length=0, pad=5)
        ax.set_xlabel(f'Residue modulo {m}', labelpad=6)
        ax.set_ylabel(f'Residue modulo {a}', labelpad=7)
        ax.set_title(f'{int(valid.sum())} compatible pairs of {m*a}', fontsize=11, pad=10, color='black')
        for spine in ax.spines.values():
            spine.set_visible(False)
    fig.savefig(ROOT / 'compatible_residue_states.png', dpi=240, facecolor='white', bbox_inches='tight')
    plt.close(fig)


def make_reference():
    doc = Document()
    sec = doc.sections[0]
    sec.page_width = Inches(8.5)
    sec.page_height = Inches(11)
    sec.top_margin = Inches(.77)
    sec.bottom_margin = Inches(.77)
    sec.left_margin = Inches(.86)
    sec.right_margin = Inches(.86)
    sec.header_distance = Inches(.32)
    sec.footer_distance = Inches(.32)
    normal = doc.styles['Normal']
    set_font(normal, FONT, 11.5)
    normal.paragraph_format.space_after = Pt(6)
    normal.paragraph_format.line_spacing = 1.1
    normal.paragraph_format.widow_control = True
    for name in ('Body Text', 'First Paragraph'):
        if name not in doc.styles:
            doc.styles.add_style(name, 1)
        set_font(doc.styles[name], FONT, 11.5)
        doc.styles[name].base_style = normal
        doc.styles[name].paragraph_format.space_after = Pt(6)
        doc.styles[name].paragraph_format.line_spacing = 1.1
        doc.styles[name].paragraph_format.widow_control = True
    if 'Compact' not in doc.styles:
        doc.styles.add_style('Compact', 1)
    doc.styles['Compact'].base_style = normal
    set_font(doc.styles['Compact'], FONT, 10.5)
    doc.styles['Compact'].paragraph_format.space_after = Pt(0)
    set_font(doc.styles['Title'], SANS, 26, True)
    doc.styles['Title'].paragraph_format.space_after = Pt(10)
    set_font(doc.styles['Subtitle'], FONT, 14)
    doc.styles['Subtitle'].paragraph_format.space_after = Pt(15)
    for level, size, before, after in [(1, 16, 17, 8), (2, 12.5, 12, 6), (3, 11.5, 10, 5)]:
        st = doc.styles[f'Heading {level}']
        set_font(st, SANS, size, True)
        st.paragraph_format.space_before = Pt(before)
        st.paragraph_format.space_after = Pt(after)
        st.paragraph_format.keep_with_next = True
        st.paragraph_format.keep_together = True
    set_font(doc.styles['Caption'], FONT, 9.5)
    doc.styles['Caption'].font.italic = False
    doc.styles['Caption'].paragraph_format.space_before = Pt(5)
    doc.styles['Caption'].paragraph_format.space_after = Pt(9)
    for name in ('Author', 'Date', 'Abstract'):
        if name not in doc.styles:
            doc.styles.add_style(name, 1)
        set_font(doc.styles[name], FONT, 11)
        doc.styles[name].paragraph_format.space_after = Pt(4)
    set_font(doc.styles['Header'], SANS, 8)
    set_font(doc.styles['Footer'], SANS, 8)
    if 'Verbatim Char' not in doc.styles:
        doc.styles.add_style('Verbatim Char', 2)
    set_font(doc.styles['Verbatim Char'], 'Liberation Mono', 9)
    settings = doc.settings.element
    mp = settings.find(qn('m:mathPr'))
    if mp is None:
        mp = OxmlElement('m:mathPr')
        settings.append(mp)
    mf = OxmlElement('m:mathFont')
    mf.set(qn('m:val'), MATH)
    mp.append(mf)
    doc.save(ROOT / 'reference.docx')


def polish():
    doc = Document(DOCX)
    for sec in doc.sections:
        sec.page_width = Inches(8.5)
        sec.page_height = Inches(11)
        sec.top_margin = Inches(.77)
        sec.bottom_margin = Inches(.77)
        sec.left_margin = Inches(.86)
        sec.right_margin = Inches(.86)
        sec.header_distance = Inches(.32)
        sec.footer_distance = Inches(.32)
        sec.different_first_page_header_footer = True
        header = sec.header.paragraphs[0]
        header.text = 'ARBITRARY MODULI IN CRAM'
        header.alignment = WD_ALIGN_PARAGRAPH.RIGHT
        for run in header.runs:
            run.font.name = SANS
            run.font.size = Pt(8)
            run.font.color.rgb = RGBColor(0, 0, 0)
        for footer in (sec.footer, sec.first_page_footer):
            p = footer.paragraphs[0]
            p.alignment = WD_ALIGN_PARAGRAPH.RIGHT
            run = p.add_run('CRAM research  |  ')
            run.font.name = SANS
            run.font.size = Pt(8)
            field = OxmlElement('w:fldSimple')
            field.set(qn('w:instr'), 'PAGE')
            p._p.append(field)
    for p in doc.paragraphs:
        p.paragraph_format.widow_control = True
        previous = p._p.getprevious()
        if previous is not None and previous.tag == qn('w:tbl'):
            p.paragraph_format.space_before = Pt(7)
        following = p._p.getnext()
        if following is not None and following.tag == qn('w:p') and following.findall('.//' + qn('m:oMathPara')):
            p.paragraph_format.keep_with_next = True
        if p.style.name in ('Title', 'Subtitle', 'Author', 'Date'):
            p.paragraph_format.keep_with_next = True
        if p.style.name == 'Title':
            p.alignment = WD_ALIGN_PARAGRAPH.LEFT
            for run in p.runs:
                run.font.color.rgb = RGBColor(0, 0, 0)
                run.font.underline = False
        if p.style.name.startswith('Heading') or p.style.name in ('Title', 'Subtitle'):
            for run in p.runs:
                run.font.color.rgb = RGBColor(0, 0, 0)
            pr = p._p.get_or_add_pPr()
            for tag in ('w:pBdr', 'w:shd'):
                for child in pr.findall(qn(tag)):
                    pr.remove(child)
        # Each numbered theorem statement stays with the next proof or display.
        if p.text.startswith('Theorem '):
            p.paragraph_format.keep_with_next = True
        if p._p.findall('.//' + qn('m:oMathPara')):
            p.paragraph_format.space_before = Pt(4)
            p.paragraph_format.space_after = Pt(8)
            p.paragraph_format.keep_together = True
            p.paragraph_format.alignment = WD_ALIGN_PARAGRAPH.CENTER
        if p._p.findall('.//' + qn('w:drawing')):
            p.paragraph_format.keep_with_next = True
        if p.style.name in ('Image Caption', 'Caption'):
            p.paragraph_format.keep_together = True
            p.paragraph_format.space_after = Pt(10)
        if p.text.startswith('[') and '] ' in p.text[:7]:
            p.paragraph_format.keep_together = True
            p.paragraph_format.space_after = Pt(7)
            p.paragraph_format.line_spacing = 1.05
            for run in p.runs:
                run.font.size = Pt(10.5)
    # Keep reference section and long appendices easy to find without blank title pages.
    for p in doc.paragraphs:
        if p.text in ('Appendix A Corrections to the disputed interpretation', 'Appendix B Formal source correspondence', 'References'):
            p.paragraph_format.page_break_before = True
    # All equations remain native OMML; choose an installed OpenType math face.
    for math_run in doc.element.body.findall('.//' + qn('m:r')):
        rpr = math_run.find(qn('w:rPr'))
        if rpr is None:
            rpr = OxmlElement('w:rPr')
            math_run.insert(0, rpr)
        rf = rpr.find(qn('w:rFonts'))
        if rf is None:
            rf = OxmlElement('w:rFonts')
            rpr.append(rf)
        rf.set(qn('w:ascii'), MATH)
        rf.set(qn('w:hAnsi'), MATH)
    widths = [
        [2.35, 2.35, 2.08],
        [1.0, 5.78],
        [1.4, 1.7, 1.9, 1.78],
        [1.55, 2.45, 2.78],
        [2.35, 4.43],
        [2.15, 4.63],
    ]
    for ti, table in enumerate(doc.tables):
        table.style = doc.styles['Table Grid']
        table.autofit = False
        table.alignment = WD_TABLE_ALIGNMENT.CENTER
        tw = widths[ti]
        pr = table._tbl.tblPr
        tblw = pr.find(qn('w:tblW'))
        if tblw is not None:
            tblw.set(qn('w:type'), 'dxa')
            tblw.set(qn('w:w'), str(round(6.78 * 1440)))
        borders = pr.find(qn('w:tblBorders'))
        if borders is None:
            borders = OxmlElement('w:tblBorders')
            pr.append(borders)
        for side in ('top','left','bottom','right','insideH','insideV'):
            el = OxmlElement('w:' + side)
            el.set(qn('w:val'), 'single')
            el.set(qn('w:sz'), '4')
            el.set(qn('w:color'), 'D9D9D9')
            borders.append(el)
        grid = table._tbl.tblGrid
        for child in list(grid):
            grid.remove(child)
        for w in tw:
            col = OxmlElement('w:gridCol')
            col.set(qn('w:w'), str(round(w * 1440)))
            grid.append(col)
        for ri, row in enumerate(table.rows):
            trpr = row._tr.get_or_add_trPr()
            no_split = OxmlElement('w:cantSplit')
            trpr.append(no_split)
            if ri == 0:
                for old in trpr.findall(qn('w:tblHeader')):
                    trpr.remove(old)
                repeat = OxmlElement('w:tblHeader')
                trpr.append(repeat)
            for ci, cell in enumerate(row.cells):
                cell.width = Inches(tw[ci])
                cell.vertical_alignment = WD_CELL_VERTICAL_ALIGNMENT.CENTER
                tcp = cell._tc.get_or_add_tcPr()
                margins = OxmlElement('w:tcMar')
                for side, value in [('top',90),('bottom',90),('left',100),('right',100)]:
                    elem = OxmlElement('w:' + side)
                    elem.set(qn('w:w'),str(value))
                    elem.set(qn('w:type'),'dxa')
                    margins.append(elem)
                tcp.append(margins)
                set_cell_shading(cell, 'E4EBEF' if ri == 0 else ('F3F5F6' if ri%2 == 0 else 'FFFFFF'))
                for p in cell.paragraphs:
                    p.style = doc.styles['Normal']
                    p.paragraph_format.space_before = Pt(0)
                    p.paragraph_format.space_after = Pt(0)
                    p.paragraph_format.line_spacing = 1.06
                    p.paragraph_format.keep_with_next = ri == 0
                    p.paragraph_format.keep_together = True
                    p.alignment = WD_ALIGN_PARAGRAPH.CENTER if ti in (1,2) and (ti == 2 or ci == 0) else WD_ALIGN_PARAGRAPH.LEFT
                    for run in p.runs:
                        if run.style.name != 'Verbatim Char':
                            run.font.name = FONT
                            run.font.size = Pt(10.5)
                        if ri == 0:
                            run.font.bold = True
                            run.font.color.rgb = RGBColor(0,0,0)
                        else:
                            run.font.color.rgb = RGBColor(0,0,0)
                    if ri == 0:
                        for mr in p._p.findall('.//' + qn('m:r')):
                            rp = mr.find(qn('w:rPr'))
                            if rp is None:
                                rp = OxmlElement('w:rPr')
                                mr.insert(0,rp)
                            color = OxmlElement('w:color')
                            color.set(qn('w:val'),'000000')
                            rp.append(color)
        # Maintain schema order for readers that parse table properties sequentially.
        def reorder(element, names):
            order = {qn('w:' + name): index for index, name in enumerate(names)}
            children = list(element)
            for child in children:
                element.remove(child)
            for child in sorted(children, key=lambda c: order.get(c.tag, len(order))):
                element.append(child)
        reorder(pr, ['tblStyle','tblpPr','tblOverlap','bidiVisual','tblStyleRowBandSize','tblStyleColBandSize','tblW','jc','tblCellSpacing','tblInd','tblBorders','shd','tblLayout','tblCellMar','tblLook','tblCaption','tblDescription'])
        for row in table.rows:
            reorder(row._tr.get_or_add_trPr(), ['cnfStyle','divId','gridBefore','gridAfter','wBefore','wAfter','cantSplit','trHeight','tblHeader','tblCellSpacing','jc','hidden'])
            for cell in row.cells:
                reorder(cell._tc.get_or_add_tcPr(), ['cnfStyle','tcW','gridSpan','hMerge','vMerge','tcBorders','shd','noWrap','tcMar','textDirection','tcFitText','vAlign','hideMark'])
    # Remove all title-style borders inherited from any Word default.
    for style in doc.styles:
        if style.type == 1 and (style.name.startswith('Heading') or style.name in ('Title','Subtitle')):
            set_font(style, style.font.name or SANS, style.font.size.pt if style.font.size else 12, bool(style.font.bold))
            for ppr in style.element.findall(qn('w:pPr')):
                for border in ppr.findall(qn('w:pBdr')):
                    ppr.remove(border)
    doc.core_properties.title = 'Arbitrary Moduli in CRAM'
    doc.core_properties.subject = 'Fixed primary structure and exact observation through dependent sister trays'
    doc.core_properties.author = 'Prepared for Anthony Diaz'
    doc.core_properties.keywords = 'CRAM, arbitrary moduli, dependent sisters, exact observability, generalized CRT'
    doc.core_properties.comments = 'Research white paper prepared with AI assistance; sources and evidence boundaries are explicit.'
    doc.save(DOCX)
    print(f'Wrote {DOCX}')
    print(f'Native equation objects: {len(doc.element.body.findall(".//" + qn("m:oMath")))}')
    print(f'Tables: {len(doc.tables)}')


if __name__ == '__main__':
    figure()
    make_reference()
    subprocess.run([
        'pandoc', str(ROOT / 'Arbitrary_Moduli_in_CRAM.md'),
        '--from=markdown+tex_math_dollars', '--to=docx',
        '--reference-doc=' + str(ROOT / 'reference.docx'),
        '--resource-path=' + str(ROOT),
        '--output=' + str(DOCX),
    ], check=True)
    polish()
