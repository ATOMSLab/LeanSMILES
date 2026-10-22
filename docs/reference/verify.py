import sys, csv, copy
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rdkit import Chem, RDLogger
RDLogger.DisableLog('rdApp.*')
import aromaticity_ref as R
TM = {Chem.BondType.SINGLE:'S', Chem.BondType.DOUBLE:'D', Chem.BondType.TRIPLE:'T', Chem.BondType.AROMATIC:'A'}

def check(smi):
    ref = Chem.MolFromSmiles(smi)
    if ref is None:
        return None, 'rdkit-fails'
    m, atoms, bonds = R.from_rdkit_unsanitized(smi)
    # sanity: neighbour order == bond index order; bond arom flag == (type A)
    for a in m.GetAtoms():
        nb=[x.GetIdx() for x in a.GetNeighbors()]
        bi=sorted(b.GetIdx() for b in a.GetBonds())
        exp=[m.GetBondWithIdx(k).GetOtherAtomIdx(a.GetIdx()) for k in bi]
        if nb!=exp: return False, 'nbr-order'
    for bd in bonds:
        if bd['arom'] != (bd['t']=='A'): return False, 'bond-arom-flag'
    try:
        bt, ar, ch, hs = R.sanitize(atoms, bonds)
    except Exception as e:
        return False, 'exc %r' % e
    errs=[]
    for k,b in enumerate(ref.GetBonds()):
        if TM.get(b.GetBondType()) != bt[k]: errs.append('bond%d %s!=%s'%(k,TM.get(b.GetBondType()),bt[k]))
    for i,a in enumerate(ref.GetAtoms()):
        if a.GetIsAromatic()!=ar[i]: errs.append('arom%d'%i)
        if a.GetFormalCharge()!=ch[i]: errs.append('chg%d'%i)
        if a.GetTotalNumHs()!=hs[i]: errs.append('H%d %d!=%d'%(i,a.GetTotalNumHs(),hs[i]))
    return (not errs), ';'.join(errs)

def run(name, smis):
    ok=0; bad=[]
    for tag,s in smis:
        r,msg=check(s)
        if r: ok+=1
        else: bad.append((tag,s,msg))
    print('%s: %d/%d' % (name, ok, len(smis)))
    for b in bad: print('   MISMATCH', b)

rows=[r for r in csv.reader(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../datasets/delaney-processed.csv')))][1:]
A=[(i,r[-1].strip()) for i,r in enumerate(rows)]
run('(a) delaney as written', A)
B=[(i,Chem.MolToSmiles(Chem.MolFromSmiles(s),kekuleSmiles=True)) for i,s in A]
run('(b) delaney kekule', B)
C=['c1ccccc1','C1=CC=CC=C1','c1cc[nH]c1','c1ccoc1','c1ccsc1','c1ccncc1','O=c1cccc[nH]1','c1ccc2ncccc2c1',
 'c1ccc2[nH]ccc2c1','C1=CC2=CC=CC=CC2=C1','c1ccc2ccccc2c1','c1ccc2cc3ccccc3cc2c1','c1ccc2c(c1)Cc1ccccc1-2',
 'c1ccc2c(c1)-c1cccc3cccc-2c13','c1cc2ccc3cccc4ccc(c1)c2c34','c1ccc(cc1)-c1ccccc1','C1=CCC=C1','C1=CC=CC=CC=C1',
 'O=C1C=CC=CC=C1','[cH-]1cccc1','c1c[nH]cn1','c1ncc2[nH]cnc2n1','Cn1cnc2c1c(=O)n(C)c(=O)n2C','c1cc[n+]([O-])cc1',
 'c1ccn(=O)cc1','O=n1ccccc1','c1ccc(cc1)[N+](=O)[O-]','c1ccc(cc1)N(=O)=O','O=c1ccocc1','O=S1C=CC=C1',
 'C1=CC=CC=CC=CC=CC=CC=CC=C1','c1ccccc1c1ccccc1','C1=CC=C2C(=C1)C=CC=C2','O=C1C=CC(=O)C=C1','c1cc2cccc3c4cccc5cccc(c(c1)c23)c54',
 'Cc1cc2nc3c(=O)[nH]c(=O)nc-3n(CC(O)C(O)C(O)CO)c2cc1C','[O-][n+]1ccccc1','C1=CC=CC2=CC=CC=C12','c1ccc2c(c1)ccc1ccccc12',
 'O=C1c2ccccc2C(=O)c2ccccc21','c1ccc2cc3cc4ccccc4cc3cc2c1','C1CCc2ccccc2C1','c1cc2ccc3ccc4ccc5ccc6ccc1c1c2c3c4c5c61',
 'OCl(=O)(=O)=O','CP(=O)=C','N=[N+]=[N-]','CN=N#N','c1ccc2c(c1)oc1ccccc12','c1ccc2c(c1)sc1ccccc12','C1=CC=C[CH+]C=C1','C1=C[CH+]1',
 'c1cc[se]c1','B1C=CC=C1','c1ccc2c(c1)[nH]c1ccccc12','O=C1NC(=O)c2ccccc12','c1ccc2nc3ccccc3cc2c1']
run('(c) hand list', [(i,s) for i,s in enumerate(C)])
