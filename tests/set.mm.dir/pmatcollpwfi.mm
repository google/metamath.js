include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cdecpmat.mm"
include "co.mm"
include "cmat.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "cn0.mm"
include "wral.mm"
include "wrex.mm"
include "cc0.mm"
include "cfz.mm"
include "cmpt.mm"
include "cgsu.mm"
include "crg.mm"
include "crngring.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "eqid.mm"
include "decpmataa0.mm"
include "syl2anc.mm"
include "wa.mm"
include "pmatcollpw.mm"
include "ad2antrr.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "ccmn.mm"
include "simp1.mm"
include "pmatring.mm"
include "ringcmn.mm"
include "syl.mm"
include "cbs.mm"
include "adantr.mm"
include "ply1ring.mm"
include "anim1i.mm"
include "cmgp.mm"
include "ply1moncl.mm"
include "simpl2.mm"
include "simpr.mm"
include "decpmatcl.mm"
include "syl3anc.mm"
include "mat2pmatbas0.mm"
include "matvscl.mm"
include "syl22anc.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "jca.mm"
include "0mat2pmat.mm"
include "sylan9eqr.mm"
include "oveq2d.mm"
include "clmod.mm"
include "csca.mm"
include "pmatlmod.mm"
include "adantlr.mm"
include "ply1crng.mm"
include "anim2i.mm"
include "3adant3.mm"
include "matsca2.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "oveq2i.mm"
include "lmodvs0.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "ex.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "imp.mm"
include "gsummptnn0fz.mm"
include "reximdva.mm"
include "mpd.mm"

theorem pmatcollpwfi
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let vn: setvar n
  let c.ex: class .^
  let c.as: class .*
  let cM: class M
  let cN: class N
  let cX: class X
  let vs: setvar s
  let vi: setvar i
  let vj: setvar j
  let va: setvar a
  let vb: setvar b
  assume pmatcollpw.p: |- P = ( Poly1 ` R )
  assume pmatcollpw.c: |- C = ( N Mat P )
  assume pmatcollpw.b: |- B = ( Base ` C )
  assume pmatcollpw.m: |- .* = ( .s ` C )
  assume pmatcollpw.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume pmatcollpw.x: |- X = ( var1 ` R )
  assume pmatcollpw.t: |- T = ( N matToPolyMat R )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint P n
  disjoint R n
  disjoint X n
  disjoint .^ n
  disjoint B s
  disjoint n s
  disjoint C n
  disjoint M s
  disjoint N s
  disjoint R s
  disjoint B i
  disjoint B j
  disjoint i j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint P i
  disjoint P j
  disjoint R i
  disjoint R j
  disjoint a i
  disjoint a j
  disjoint b i
  disjoint b j
  disjoint i n
  disjoint j n
  disjoint B a
  disjoint B b
  disjoint a b
  disjoint a n
  disjoint b n
  disjoint M a
  disjoint M b
  disjoint N a
  disjoint N b
  disjoint P a
  disjoint P b
  disjoint R a
  disjoint R b
  disjoint T a
  disjoint T b
  disjoint X a
  disjoint X b
  disjoint X i
  disjoint X j
  disjoint .* a
  disjoint .* b
  disjoint .^ a
  disjoint .^ b
  disjoint .^ i
  disjoint .^ j
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> E. s e. NN0 M = ( C gsum ( n e. ( 0 ... s ) |-> ( ( n .^ X ) .* ( T ` ( M decompPMat n ) ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    vs
    cv
    #
    vn
    cv
    #
    clt
    wbr
    #
    cM
    @5
    cdecpmat
    co
    #
    cN
    cR
    cmat
    co
    #
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vn
    cn0
    wral
    #
    vs
    cn0
    wrex
    #
    cM
    cC
    vn
    cc0
    @4
    cfz
    co
    @5
    cX
    c.ex
    co
    #
    @7
    cT
    cfv
    #
    c.as
    co
    #
    cmpt
    cgsu
    co
    #
    wceq
    #
    vs
    cn0
    wrex
    @3
    cR
    crg
    wcel
    #
    @2
    @13
    @1
    @0
    @19
    @2
    cR
    crngring
    3ad2ant2
    #
    @0
    @1
    @2
    simp3
    #
    vn
    @8
    cB
    cC
    cP
    cR
    cM
    cN
    @9
    vs
    pmatcollpw.p
    pmatcollpw.c
    pmatcollpw.b
    @8
    eqid
    #
    @9
    eqid
    #
    decpmataa0
    syl2anc
    @3
    @12
    @18
    vs
    cn0
    @3
    @4
    cn0
    wcel
    #
    wa
    #
    @12
    @18
    @25
    @12
    wa
    #
    cM
    cC
    vn
    cn0
    @16
    cmpt
    cgsu
    co
    #
    @17
    @3
    cM
    @27
    wceq
    @24
    @12
    cB
    cC
    cP
    cR
    cT
    vn
    c.ex
    c.as
    cM
    cN
    cX
    pmatcollpw.p
    pmatcollpw.c
    pmatcollpw.b
    pmatcollpw.m
    pmatcollpw.e
    pmatcollpw.x
    pmatcollpw.t
    pmatcollpw
    ad2antrr
    @26
    cB
    @16
    @4
    vn
    cC
    cC
    c0g
    cfv
    #
    @25
    @12
    vn
    @25
    vn
    nfv
    @11
    vn
    cn0
    nfra1
    nfan
    pmatcollpw.b
    @28
    eqid
    #
    @3
    cC
    ccmn
    wcel
    #
    @24
    @12
    @3
    cC
    crg
    wcel
    #
    @30
    @3
    @0
    @19
    @31
    @0
    @1
    @2
    simp1
    #
    @20
    cC
    cP
    cR
    cN
    pmatcollpw.p
    pmatcollpw.c
    pmatring
    syl2anc
    cC
    ringcmn
    syl
    ad2antrr
    @3
    @16
    cB
    wcel
    #
    vn
    cn0
    wral
    @24
    @12
    @3
    @33
    vn
    cn0
    @3
    @5
    cn0
    wcel
    #
    wa
    #
    @0
    cP
    crg
    wcel
    #
    @14
    cP
    cbs
    cfv
    #
    wcel
    #
    @15
    cB
    wcel
    #
    @33
    @3
    @0
    @34
    @32
    adantr
    #
    @35
    @19
    @36
    @3
    @19
    @34
    @20
    adantr
    #
    cP
    cR
    pmatcollpw.p
    ply1ring
    syl
    @35
    @19
    @34
    wa
    #
    @38
    @3
    @19
    @34
    @20
    anim1i
    #
    @37
    @5
    cP
    cR
    c.ex
    cP
    cmgp
    cfv
    #
    cX
    pmatcollpw.p
    pmatcollpw.x
    @44
    eqid
    pmatcollpw.e
    @37
    eqid
    #
    ply1moncl
    #
    syl
    @35
    @0
    @19
    @7
    @8
    cbs
    cfv
    #
    wcel
    #
    @39
    @40
    @41
    @35
    @1
    @2
    @34
    @48
    @0
    @1
    @2
    @34
    simpl2
    @3
    @2
    @34
    @21
    adantr
    @3
    @34
    simpr
    @8
    cB
    cC
    @47
    cP
    cR
    @5
    cM
    cN
    ccrg
    pmatcollpw.p
    pmatcollpw.c
    pmatcollpw.b
    @22
    @47
    eqid
    #
    decpmatcl
    syl3anc
    @8
    @47
    cC
    cP
    cR
    cT
    cB
    @7
    cN
    pmatcollpw.t
    @22
    @49
    pmatcollpw.p
    pmatcollpw.c
    pmatcollpw.b
    mat2pmatbas0
    syl3anc
    cC
    cB
    @14
    cP
    c.as
    @37
    cN
    @15
    @45
    pmatcollpw.c
    pmatcollpw.b
    pmatcollpw.m
    matvscl
    syl22anc
    ralrimiva
    ad2antrr
    @25
    @24
    @12
    @3
    @24
    simpr
    adantr
    @25
    @12
    @6
    @16
    @28
    wceq
    #
    wi
    #
    vn
    cn0
    wral
    @25
    @11
    @51
    vn
    cn0
    @25
    @34
    wa
    #
    @10
    @50
    @6
    @52
    @10
    @50
    @52
    @10
    wa
    #
    @16
    @14
    cN
    cP
    cmat
    co
    #
    c0g
    cfv
    #
    c.as
    co
    #
    @28
    @53
    @15
    @55
    @14
    c.as
    @10
    @52
    @15
    @9
    cT
    cfv
    #
    @55
    @7
    @9
    cT
    fveq2
    @52
    @19
    @0
    wa
    #
    @57
    @55
    wceq
    @3
    @58
    @24
    @34
    @3
    @19
    @0
    @20
    @32
    jca
    ad2antrr
    cP
    cR
    cT
    cN
    @9
    @55
    pmatcollpw.t
    pmatcollpw.p
    @23
    @55
    eqid
    0mat2pmat
    syl
    sylan9eqr
    oveq2d
    @52
    @56
    @28
    wceq
    #
    @10
    @52
    cC
    clmod
    wcel
    #
    @14
    cC
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @59
    @3
    @60
    @24
    @34
    @3
    @0
    @19
    @60
    @32
    @20
    cC
    cP
    cR
    cN
    pmatcollpw.p
    pmatcollpw.c
    pmatlmod
    syl2anc
    ad2antrr
    @52
    @14
    @37
    @62
    @52
    @42
    @38
    @3
    @34
    @42
    @24
    @43
    adantlr
    @46
    syl
    @52
    @61
    cP
    cbs
    @3
    @61
    cP
    wceq
    @24
    @34
    @3
    cP
    @61
    @3
    @0
    cP
    ccrg
    wcel
    #
    wa
    #
    cP
    @61
    wceq
    @0
    @1
    @65
    @2
    @1
    @64
    @0
    cP
    cR
    pmatcollpw.p
    ply1crng
    anim2i
    3adant3
    cC
    cP
    cN
    ccrg
    pmatcollpw.c
    matsca2
    syl
    eqcomd
    ad2antrr
    fveq2d
    eleqtrrd
    @60
    @63
    wa
    @56
    @14
    @28
    c.as
    co
    @28
    @55
    @28
    @14
    c.as
    @54
    cC
    c0g
    cC
    @54
    pmatcollpw.c
    eqcomi
    fveq2i
    oveq2i
    c.as
    @61
    @62
    cC
    @14
    @28
    @61
    eqid
    pmatcollpw.m
    @62
    eqid
    @29
    lmodvs0
    syl5eq
    syl2anc
    adantr
    eqtrd
    ex
    imim2d
    ralimdva
    imp
    gsummptnn0fz
    eqtrd
    ex
    reximdva
    mpd
end
