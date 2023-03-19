include "crg.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "w3a.mm"
include "cur.mm"
include "cfv.mm"
include "cvsca.mm"
include "co.mm"
include "csg.mm"
include "cbs.mm"
include "ply1ring.mm"
include "3ad2ant1.mm"
include "clmod.mm"
include "csca.mm"
include "cfn.mm"
include "snfi.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "adantr.mm"
include "anim12i.mm"
include "3adant3.mm"
include "ancomd.mm"
include "matlmod.mm"
include "syl.mm"
include "cpl1.mm"
include "eqid.mm"
include "vr1cl.mm"
include "cvv.mm"
include "3ad2ant2.mm"
include "fvex.mm"
include "cmat.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "matsca2.mm"
include "sylancl.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "matring.mm"
include "ringidcl.mm"
include "3jca.mm"
include "lmodvscl.mm"
include "simp1.mm"
include "simp3.mm"
include "mat2pmatbas.mm"
include "snidg.mm"
include "adantl.mm"
include "wb.mm"
include "eleq2.mm"
include "mpbird.mm"
include "id.mm"
include "jccir.mm"
include "matsubgcell.mm"
include "syl121anc.mm"
include "cmulr.mm"
include "matvscacell.mm"
include "c0g.mm"
include "cif.mm"
include "mat1ov.mm"
include "eqidd.mm"
include "iftrued.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "ringridm.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "mat2pmatvalel.mm"
include "oveq12d.mm"

theorem chpmat1dlem
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cG: class G
  let cI: class I
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cX: class X
  assume chpmat1d.c: |- C = ( N CharPlyMat R )
  assume chpmat1d.p: |- P = ( Poly1 ` R )
  assume chpmat1d.a: |- A = ( N Mat R )
  assume chpmat1d.b: |- B = ( Base ` A )
  assume chpmat1d.x: |- X = ( var1 ` R )
  assume chpmat1d.z: |- .- = ( -g ` P )
  assume chpmat1d.s: |- S = ( algSc ` P )
  assume chpmat1dlem.g: |- G = ( N Mat P )
  assume chpmat1dlem.x: |- T = ( N matToPolyMat R )


  assert |- ( ( R e. Ring /\ ( N = { I } /\ I e. V ) /\ M e. B ) -> ( I ( ( X ( .s ` G ) ( 1r ` G ) ) ( -g ` G ) ( T ` M ) ) I ) = ( X .- ( S ` ( I M I ) ) ) )

  proof
    cR
    crg
    wcel
    #
    cN
    cI
    csn
    #
    wceq
    #
    cI
    cV
    wcel
    #
    wa
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cI
    cI
    cX
    cG
    cur
    cfv
    #
    cG
    cvsca
    cfv
    #
    co
    #
    cM
    cT
    cfv
    #
    cG
    csg
    cfv
    #
    co
    co
    #
    cI
    cI
    @9
    co
    #
    cI
    cI
    @10
    co
    #
    c.mi
    co
    #
    cX
    cI
    cI
    cM
    co
    cS
    cfv
    #
    c.mi
    co
    @6
    cP
    crg
    wcel
    #
    @9
    cG
    cbs
    cfv
    #
    wcel
    #
    @10
    @18
    wcel
    #
    cI
    cN
    wcel
    #
    @21
    wa
    #
    @12
    @15
    wceq
    @0
    @4
    @17
    @5
    cP
    cR
    chpmat1d.p
    ply1ring
    #
    3ad2ant1
    #
    @6
    cG
    clmod
    wcel
    #
    cX
    cG
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @7
    @18
    wcel
    #
    w3a
    @19
    @6
    @25
    @28
    @29
    @6
    cN
    cfn
    wcel
    #
    @17
    wa
    #
    @25
    @6
    @17
    @30
    @0
    @4
    @17
    @30
    wa
    @5
    @0
    @17
    @4
    @30
    @23
    @2
    @30
    @3
    @2
    @30
    @1
    cfn
    wcel
    cI
    snfi
    cN
    @1
    cfn
    eleq1
    mpbiri
    adantr
    #
    anim12i
    3adant3
    ancomd
    #
    cG
    cP
    cN
    chpmat1dlem.g
    matlmod
    syl
    @6
    cX
    cR
    cpl1
    cfv
    #
    cbs
    cfv
    #
    @27
    @0
    @4
    cX
    @35
    wcel
    @5
    @35
    @34
    cR
    cX
    chpmat1d.x
    @34
    eqid
    @35
    eqid
    vr1cl
    3ad2ant1
    @6
    @26
    @34
    cbs
    @6
    @34
    @26
    @6
    @30
    @34
    cvv
    wcel
    @34
    @26
    wceq
    @4
    @0
    @30
    @5
    @32
    3ad2ant2
    #
    cR
    cpl1
    fvex
    cG
    @34
    cN
    cvv
    cG
    cN
    cP
    cmat
    co
    cN
    @34
    cmat
    co
    chpmat1dlem.g
    cP
    @34
    cN
    cmat
    chpmat1d.p
    oveq2i
    eqtri
    matsca2
    sylancl
    eqcomd
    fveq2d
    eleqtrrd
    @6
    cG
    crg
    wcel
    #
    @29
    @6
    @31
    @37
    @33
    cG
    cP
    cN
    chpmat1dlem.g
    matring
    syl
    @18
    cG
    @7
    @18
    eqid
    #
    @7
    eqid
    #
    ringidcl
    syl
    #
    3jca
    cX
    @8
    @26
    @27
    @18
    cG
    @7
    @38
    @26
    eqid
    @8
    eqid
    #
    @27
    eqid
    lmodvscl
    syl
    @6
    @30
    @0
    @5
    w3a
    #
    @20
    @6
    @30
    @0
    @5
    @36
    @0
    @4
    @5
    simp1
    @0
    @4
    @5
    simp3
    3jca
    #
    cA
    cB
    cG
    cP
    cR
    cT
    cM
    cN
    chpmat1dlem.x
    chpmat1d.a
    chpmat1d.b
    chpmat1d.p
    chpmat1dlem.g
    mat2pmatbas
    syl
    @4
    @0
    @22
    @5
    @4
    @21
    @21
    @4
    @21
    cI
    @1
    wcel
    #
    @3
    @44
    @2
    cI
    cV
    snidg
    adantl
    @2
    @21
    @44
    wb
    @3
    cN
    @1
    cI
    eleq2
    adantr
    mpbird
    #
    @21
    id
    jccir
    3ad2ant2
    #
    cG
    @18
    cP
    @11
    cI
    cI
    c.mi
    cN
    @9
    @10
    chpmat1dlem.g
    @38
    @11
    eqid
    chpmat1d.z
    matsubgcell
    syl121anc
    @6
    @13
    cX
    @14
    @16
    c.mi
    @6
    @13
    cX
    cI
    cI
    @7
    co
    #
    cP
    cmulr
    cfv
    #
    co
    #
    cX
    cP
    cur
    cfv
    #
    @48
    co
    #
    cX
    @6
    @17
    cX
    cP
    cbs
    cfv
    #
    wcel
    #
    @29
    @22
    @13
    @49
    wceq
    @24
    @0
    @4
    @53
    @5
    @52
    cP
    cR
    cX
    chpmat1d.x
    chpmat1d.p
    @52
    eqid
    #
    vr1cl
    3ad2ant1
    #
    @40
    @46
    cG
    @18
    cP
    @8
    @48
    cI
    cI
    @52
    cN
    cX
    @7
    chpmat1dlem.g
    @38
    @54
    @41
    @48
    eqid
    #
    matvscacell
    syl121anc
    @6
    @47
    @50
    cX
    @48
    @6
    @47
    cI
    cI
    wceq
    #
    @50
    cP
    c0g
    cfv
    #
    cif
    @50
    @6
    cG
    cP
    @7
    @50
    cI
    cI
    cN
    @58
    chpmat1dlem.g
    @50
    eqid
    #
    @58
    eqid
    @36
    @24
    @4
    @0
    @21
    @5
    @45
    3ad2ant2
    #
    @60
    @39
    mat1ov
    @6
    @57
    @50
    @58
    @6
    cI
    eqidd
    iftrued
    eqtrd
    oveq2d
    @6
    @17
    @53
    @51
    cX
    wceq
    @24
    @55
    @52
    cP
    @48
    @50
    cX
    @54
    @56
    @59
    ringridm
    syl2anc
    3eqtrd
    @6
    @42
    @22
    @14
    @16
    wceq
    @43
    @46
    cA
    cB
    cP
    cR
    cS
    cT
    cM
    cN
    crg
    cI
    cI
    chpmat1dlem.x
    chpmat1d.a
    chpmat1d.b
    chpmat1d.p
    chpmat1d.s
    mat2pmatvalel
    syl2anc
    oveq12d
    eqtrd
end
