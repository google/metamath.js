include "ccrg.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "cv1.mm"
include "cmat.mm"
include "co.mm"
include "cur.mm"
include "cvsca.mm"
include "cmat2pmat.mm"
include "csg.mm"
include "cmdat.mm"
include "cfn.mm"
include "snfi.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "adantr.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "simp3.mm"
include "eqid.mm"
include "chpmatval.mm"
include "syl3anc.mm"
include "cbs.mm"
include "ply1crng.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "cgrp.mm"
include "crg.mm"
include "crngring.mm"
include "ply1ring.mm"
include "syl.mm"
include "matring.mm"
include "syl2anc.mm"
include "ringgrp.mm"
include "clmod.mm"
include "csca.mm"
include "matlmod.mm"
include "cpl1.mm"
include "vr1cl.mm"
include "oveq2i.mm"
include "matsca2.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "ringidcl.mm"
include "lmodvscl.mm"
include "mat2pmatbas.mm"
include "grpsubcl.mm"
include "m1detdiag.mm"
include "eqcomi.mm"
include "a1i.mm"
include "oveq1d.mm"
include "oveqd.mm"
include "chpmat1dlem.mm"
include "syl3an1.mm"
include "eqtrd.mm"

theorem chpmat1d
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
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


  assert |- ( ( R e. CRing /\ ( N = { I } /\ I e. V ) /\ M e. B ) -> ( C ` M ) = ( X .- ( S ` ( I M I ) ) ) )

  proof
    cR
    ccrg
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
    cM
    cC
    cfv
    #
    cR
    cv1
    cfv
    #
    cN
    cP
    cmat
    co
    #
    cur
    cfv
    #
    @9
    cvsca
    cfv
    #
    co
    #
    cM
    cN
    cR
    cmat2pmat
    co
    #
    cfv
    #
    @9
    csg
    cfv
    #
    co
    #
    cN
    cP
    cmdat
    co
    #
    cfv
    #
    cX
    cI
    cI
    cM
    co
    cS
    cfv
    c.mi
    co
    #
    @6
    cN
    cfn
    wcel
    #
    @0
    @5
    @7
    @18
    wceq
    @4
    @0
    @20
    @5
    @2
    @20
    @3
    @2
    @20
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
    3ad2ant2
    #
    @0
    @4
    @5
    simp1
    @0
    @4
    @5
    simp3
    #
    cA
    cB
    cC
    @17
    cP
    cR
    @13
    @11
    @10
    cM
    @15
    cN
    ccrg
    @8
    @9
    chpmat1d.c
    chpmat1d.a
    chpmat1d.b
    chpmat1d.p
    @9
    eqid
    #
    @17
    eqid
    #
    @15
    eqid
    #
    @8
    eqid
    #
    @11
    eqid
    #
    @13
    eqid
    #
    @10
    eqid
    #
    chpmatval
    syl3anc
    @6
    @18
    cI
    cI
    @16
    co
    #
    @19
    @6
    cP
    ccrg
    wcel
    #
    @4
    @16
    @9
    cbs
    cfv
    #
    wcel
    #
    @18
    @30
    wceq
    @0
    @4
    @31
    @5
    cP
    cR
    chpmat1d.p
    ply1crng
    3ad2ant1
    @0
    @4
    @5
    simp2
    @6
    @9
    cgrp
    wcel
    #
    @12
    @32
    wcel
    #
    @14
    @32
    wcel
    #
    @33
    @6
    @9
    crg
    wcel
    #
    @34
    @6
    @20
    cP
    crg
    wcel
    #
    @37
    @21
    @0
    @4
    @38
    @5
    @0
    cR
    crg
    wcel
    #
    @38
    cR
    crngring
    #
    cP
    cR
    chpmat1d.p
    ply1ring
    syl
    3ad2ant1
    #
    @9
    cP
    cN
    @23
    matring
    syl2anc
    #
    @9
    ringgrp
    syl
    @6
    @9
    clmod
    wcel
    #
    @8
    @9
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @10
    @32
    wcel
    #
    @35
    @6
    @20
    @38
    @43
    @21
    @41
    @9
    cP
    cN
    @23
    matlmod
    syl2anc
    @6
    @8
    cR
    cpl1
    cfv
    #
    cbs
    cfv
    #
    @45
    @6
    @39
    @8
    @48
    wcel
    @0
    @4
    @39
    @5
    @40
    3ad2ant1
    #
    @48
    @47
    cR
    @8
    @26
    @47
    eqid
    #
    @48
    eqid
    vr1cl
    syl
    @6
    @44
    @47
    cbs
    @6
    @47
    @44
    @6
    @20
    @47
    ccrg
    wcel
    #
    @47
    @44
    wceq
    @21
    @0
    @4
    @51
    @5
    @47
    cR
    @50
    ply1crng
    3ad2ant1
    @9
    @47
    cN
    ccrg
    cP
    @47
    cN
    cmat
    chpmat1d.p
    oveq2i
    matsca2
    syl2anc
    eqcomd
    fveq2d
    eleqtrrd
    @6
    @37
    @46
    @42
    @32
    @9
    @10
    @32
    eqid
    #
    @29
    ringidcl
    syl
    @8
    @11
    @44
    @45
    @32
    @9
    @10
    @52
    @44
    eqid
    @27
    @45
    eqid
    lmodvscl
    syl3anc
    @6
    @20
    @39
    @5
    @36
    @21
    @49
    @22
    cA
    cB
    @9
    cP
    cR
    @13
    cM
    cN
    @28
    chpmat1d.a
    chpmat1d.b
    chpmat1d.p
    @23
    mat2pmatbas
    syl3anc
    @32
    @9
    @15
    @12
    @14
    @52
    @25
    grpsubcl
    syl3anc
    @9
    @32
    @17
    cP
    cI
    @16
    cN
    cV
    @24
    @23
    @52
    m1detdiag
    syl3anc
    @6
    @30
    cI
    cI
    cX
    @10
    @11
    co
    #
    @14
    @15
    co
    #
    co
    #
    @19
    @6
    @16
    @54
    cI
    cI
    @6
    @12
    @53
    @14
    @15
    @6
    @8
    cX
    @10
    @11
    @8
    cX
    wceq
    @6
    cX
    @8
    chpmat1d.x
    eqcomi
    a1i
    oveq1d
    oveq1d
    oveqd
    @0
    @39
    @4
    @5
    @55
    @19
    wceq
    @40
    cA
    cB
    cC
    cP
    cR
    cS
    @13
    @9
    cI
    cM
    c.mi
    cN
    cV
    cX
    chpmat1d.c
    chpmat1d.p
    chpmat1d.a
    chpmat1d.b
    chpmat1d.x
    chpmat1d.z
    chpmat1d.s
    @23
    @28
    chpmat1dlem
    syl3an1
    eqtrd
    eqtrd
    eqtrd
end
