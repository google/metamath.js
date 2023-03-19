include "co.mm"
include "cmpt.mm"
include "climc.mm"
include "wcel.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "crest.mm"
include "ccnp.mm"
include "cfv.mm"
include "cop.mm"
include "ccom.mm"
include "cxp.mm"
include "wa.mm"
include "cuni.mm"
include "eqid.mm"
include "cnprcl.mm"
include "syl.mm"
include "ctopon.mm"
include "ctx.mm"
include "cc.mm"
include "wss.mm"
include "cnfldtopon.mm"
include "txtopon.mm"
include "mp2an.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "resttopon.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "toponuni.mm"
include "eleqtrrd.mm"
include "opelxp.mm"
include "sylib.mm"
include "simpld.mm"
include "ad2antrr.mm"
include "wn.mm"
include "simpll.mm"
include "wo.mm"
include "simpr.mm"
include "elun.mm"
include "ord.mm"
include "elsni.mm"
include "syl6.mm"
include "con1d.mm"
include "imp.mm"
include "ifclda.mm"
include "simprd.mm"
include "opelxpi.mm"
include "eqidd.mm"
include "wf.mm"
include "a1i.mm"
include "cnpf2.mm"
include "syl3anc.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "df-ov.mm"
include "ovif12.mm"
include "eqtr3i.mm"
include "syl6eq.mm"
include "fmptco.mm"
include "cdm.mm"
include "dmmptd.mm"
include "w3a.mm"
include "limcrcl.mm"
include "simp2d.mm"
include "eqsstr3d.mm"
include "simp3d.mm"
include "snssd.mm"
include "unssd.mm"
include "ssun2.mm"
include "wb.mm"
include "snssg.mm"
include "mpbiri.mm"
include "adantr.mm"
include "sseldd.mm"
include "limcmpt.mm"
include "mpbid.mm"
include "txcnp.mm"
include "ctop.mm"
include "topontopi.mm"
include "fmptd.mm"
include "feq2d.mm"
include "toponunii.mm"
include "cnprest2.mm"
include "oveq2i.mm"
include "fveq1i.mm"
include "syl6eleqr.mm"
include "iftrue.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"
include "fveq2d.mm"
include "cnpco.mm"
include "eqeltrrd.mm"
include "fovrnd.mm"
include "mpbird.mm"

theorem limccnp2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cH: class H
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vy: setvar y
  assume limccnp2.r: |- ( ( ph /\ x e. A ) -> R e. X )
  assume limccnp2.s: |- ( ( ph /\ x e. A ) -> S e. Y )
  assume limccnp2.x: |- ( ph -> X C_ CC )
  assume limccnp2.y: |- ( ph -> Y C_ CC )
  assume limccnp2.k: |- K = ( TopOpen ` CCfld )
  assume limccnp2.j: |- J = ( ( K tX K ) |`t ( X X. Y ) )
  assume limccnp2.c: |- ( ph -> C e. ( ( x e. A |-> R ) limCC B ) )
  assume limccnp2.d: |- ( ph -> D e. ( ( x e. A |-> S ) limCC B ) )
  assume limccnp2.h: |- ( ph -> H e. ( ( J CnP K ) ` <. C , D >. ) )

  disjoint B x
  disjoint C x
  disjoint D x
  disjoint H x
  disjoint ph x
  disjoint X x
  disjoint A x
  disjoint Y x
  disjoint x y
  disjoint B y
  disjoint C y
  disjoint D y
  disjoint H y
  disjoint X y
  disjoint R y
  disjoint S y
  disjoint Y y
  assert |- ( ph -> ( C H D ) e. ( ( x e. A |-> ( R H S ) ) limCC B ) )

  proof
    wph
    cC
    cD
    cH
    co
    #
    vx
    cA
    cR
    cS
    cH
    co
    #
    cmpt
    cB
    climc
    co
    wcel
    vx
    cA
    cB
    csn
    #
    cun
    #
    vx
    cv
    #
    cB
    wceq
    #
    @0
    @1
    cif
    #
    cmpt
    #
    cB
    cK
    @3
    crest
    co
    #
    cK
    ccnp
    co
    cfv
    #
    wcel
    wph
    cH
    vx
    @3
    @5
    cC
    cR
    cif
    #
    @5
    cD
    cS
    cif
    #
    cop
    #
    cmpt
    #
    ccom
    #
    @7
    @9
    wph
    vx
    vy
    @3
    cX
    cY
    cxp
    #
    @12
    vy
    cv
    #
    cH
    cfv
    #
    @6
    @13
    cH
    wph
    @4
    @3
    wcel
    #
    wa
    #
    @10
    cX
    wcel
    @11
    cY
    wcel
    @12
    @15
    wcel
    @19
    @5
    cC
    cR
    cX
    wph
    cC
    cX
    wcel
    #
    @18
    @5
    wph
    @20
    cD
    cY
    wcel
    #
    wph
    cC
    cD
    cop
    #
    @15
    wcel
    @20
    @21
    wa
    wph
    @22
    cJ
    cuni
    #
    @15
    wph
    cH
    @22
    cJ
    cK
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    @22
    @23
    wcel
    limccnp2.h
    @22
    cH
    cJ
    cK
    @23
    @23
    eqid
    cnprcl
    syl
    wph
    cJ
    @15
    ctopon
    cfv
    #
    wcel
    #
    @15
    @23
    wceq
    wph
    cJ
    cK
    cK
    ctx
    co
    #
    @15
    crest
    co
    #
    @27
    limccnp2.j
    wph
    @29
    cc
    cc
    cxp
    #
    ctopon
    cfv
    wcel
    #
    @15
    @31
    wss
    #
    @30
    @27
    wcel
    cK
    cc
    ctopon
    cfv
    wcel
    #
    @34
    @32
    cK
    limccnp2.k
    cnfldtopon
    #
    @35
    cK
    cK
    cc
    cc
    txtopon
    mp2an
    #
    wph
    cX
    cc
    wss
    #
    cY
    cc
    wss
    #
    @33
    limccnp2.x
    limccnp2.y
    cX
    cc
    cY
    cc
    xpss12
    syl2anc
    #
    @15
    @29
    @31
    resttopon
    sylancr
    syl5eqel
    #
    @15
    cJ
    toponuni
    syl
    eleqtrrd
    cC
    cD
    cX
    cY
    opelxp
    sylib
    #
    simpld
    ad2antrr
    @19
    @5
    wn
    #
    wa
    #
    wph
    @4
    cA
    wcel
    #
    cR
    cX
    wcel
    wph
    @18
    @42
    simpll
    #
    @19
    @42
    @44
    @19
    @44
    @5
    @19
    @44
    wn
    @4
    @2
    wcel
    #
    @5
    @19
    @44
    @46
    @19
    @18
    @44
    @46
    wo
    wph
    @18
    simpr
    @4
    cA
    @2
    elun
    sylib
    ord
    @4
    cB
    elsni
    syl6
    con1d
    imp
    #
    limccnp2.r
    syl2anc
    ifclda
    @19
    @5
    cD
    cS
    cY
    wph
    @21
    @18
    @5
    wph
    @20
    @21
    @41
    simprd
    ad2antrr
    @43
    wph
    @44
    cS
    cY
    wcel
    @45
    @47
    limccnp2.s
    syl2anc
    ifclda
    @10
    @11
    cX
    cY
    opelxpi
    syl2anc
    #
    wph
    @13
    eqidd
    wph
    vy
    @15
    cc
    cH
    wph
    @28
    @34
    @26
    @15
    cc
    cH
    wf
    #
    @40
    @34
    wph
    @35
    a1i
    #
    limccnp2.h
    @22
    cH
    cJ
    cK
    @15
    cc
    cnpf2
    syl3anc
    #
    feqmptd
    @16
    @12
    wceq
    @17
    @12
    cH
    cfv
    #
    @6
    @16
    @12
    cH
    fveq2
    @10
    @11
    cH
    co
    @52
    @6
    @10
    @11
    cH
    df-ov
    @5
    cC
    cR
    cD
    cS
    cH
    ovif12
    eqtr3i
    syl6eq
    fmptco
    wph
    @13
    cB
    @8
    cJ
    ccnp
    co
    #
    cfv
    #
    wcel
    cH
    cB
    @13
    cfv
    #
    @24
    cfv
    #
    wcel
    @14
    @9
    wcel
    wph
    @13
    cB
    @8
    @30
    ccnp
    co
    #
    cfv
    #
    @54
    wph
    @13
    cB
    @8
    @29
    ccnp
    co
    cfv
    wcel
    #
    @13
    @58
    wcel
    #
    wph
    vx
    @10
    @11
    cB
    @8
    cK
    cK
    @3
    cc
    cc
    wph
    @34
    @3
    cc
    wss
    @8
    @3
    ctopon
    cfv
    wcel
    #
    @35
    wph
    cA
    @2
    cc
    wph
    cA
    vx
    cA
    cR
    cmpt
    #
    cdm
    #
    cc
    wph
    vx
    @62
    cA
    cR
    cX
    @62
    eqid
    limccnp2.r
    dmmptd
    wph
    @63
    cc
    @62
    wf
    #
    @63
    cc
    wss
    #
    cB
    cc
    wcel
    #
    wph
    cC
    @62
    cB
    climc
    co
    wcel
    #
    @64
    @65
    @66
    w3a
    limccnp2.c
    cB
    cC
    @62
    limcrcl
    syl
    #
    simp2d
    eqsstr3d
    #
    wph
    cB
    cc
    wph
    @64
    @65
    @66
    @68
    simp3d
    #
    snssd
    unssd
    @3
    cK
    cc
    resttopon
    sylancr
    #
    @50
    @50
    wph
    cB
    @3
    wcel
    #
    @2
    @3
    wss
    #
    @2
    cA
    ssun2
    wph
    @66
    @72
    @73
    wb
    @70
    cB
    @3
    cc
    snssg
    syl
    mpbiri
    #
    wph
    @67
    vx
    @3
    @10
    cmpt
    @9
    wcel
    limccnp2.c
    wph
    vx
    cA
    cB
    cC
    cR
    @8
    cK
    @69
    @70
    wph
    @44
    wa
    #
    cX
    cc
    cR
    wph
    @37
    @44
    limccnp2.x
    adantr
    limccnp2.r
    sseldd
    @8
    eqid
    #
    limccnp2.k
    limcmpt
    mpbid
    wph
    cD
    vx
    cA
    cS
    cmpt
    cB
    climc
    co
    wcel
    vx
    @3
    @11
    cmpt
    @9
    wcel
    limccnp2.d
    wph
    vx
    cA
    cB
    cD
    cS
    @8
    cK
    @69
    @70
    @75
    cY
    cc
    cS
    wph
    @38
    @44
    limccnp2.y
    adantr
    limccnp2.s
    sseldd
    @76
    limccnp2.k
    limcmpt
    mpbid
    txcnp
    wph
    @29
    ctop
    wcel
    #
    @8
    cuni
    #
    @15
    @13
    wf
    #
    @33
    @59
    @60
    wb
    @77
    wph
    @31
    @29
    @36
    topontopi
    a1i
    wph
    @3
    @15
    @13
    wf
    @79
    wph
    vx
    @3
    @12
    @15
    @13
    @48
    @13
    eqid
    #
    fmptd
    wph
    @3
    @78
    @15
    @13
    wph
    @61
    @3
    @78
    wceq
    @71
    @3
    @8
    toponuni
    syl
    feq2d
    mpbid
    @39
    @15
    cB
    @13
    @8
    @29
    @78
    @31
    @78
    eqid
    @31
    @29
    @36
    toponunii
    cnprest2
    syl3anc
    mpbid
    cB
    @53
    @57
    cJ
    @30
    @8
    ccnp
    limccnp2.j
    oveq2i
    fveq1i
    syl6eleqr
    wph
    cH
    @25
    @56
    limccnp2.h
    wph
    @55
    @22
    @24
    wph
    @72
    @55
    @22
    wceq
    @74
    vx
    cB
    @12
    @22
    @3
    @13
    @5
    @10
    cC
    @11
    cD
    @5
    cC
    cR
    iftrue
    @5
    cD
    cS
    iftrue
    opeq12d
    @80
    cC
    cD
    opex
    fvmpt
    syl
    fveq2d
    eleqtrrd
    cB
    @13
    cH
    @8
    cJ
    cK
    cnpco
    syl2anc
    eqeltrrd
    wph
    vx
    cA
    cB
    @0
    @1
    @8
    cK
    @69
    @70
    @75
    cR
    cS
    cc
    cX
    cY
    cH
    wph
    @49
    @44
    @51
    adantr
    limccnp2.r
    limccnp2.s
    fovrnd
    @76
    limccnp2.k
    limcmpt
    mpbird
end
