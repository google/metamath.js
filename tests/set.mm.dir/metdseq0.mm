include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cc0.mm"
include "wceq.mm"
include "ccl.mm"
include "wa.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "cbl.mm"
include "co.mm"
include "crp.mm"
include "wrex.mm"
include "simpll1.mm"
include "simprl.mm"
include "simprr.mm"
include "mopni2.mm"
include "syl3anc.mm"
include "ssrin.mm"
include "syl.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "clt.mm"
include "rpgt0.mm"
include "cr.mm"
include "wb.mm"
include "0re.mm"
include "rpre.mm"
include "ltnle.mm"
include "sylancr.mm"
include "mpbid.mm"
include "ad2antrl.mm"
include "simpllr.mm"
include "breq2d.mm"
include "cxr.mm"
include "adantr.mm"
include "simpl2.mm"
include "ad2antrr.mm"
include "simpl3.mm"
include "rpxr.mm"
include "metdsge.mm"
include "syl31anc.mm"
include "bitr3d.mm"
include "incom.mm"
include "eqeq1i.mm"
include "syl6bb.mm"
include "necon3bbid.mm"
include "ssn0.mm"
include "syl2anc.mm"
include "rexlimddv.mm"
include "expr.mm"
include "ralrimiva.mm"
include "ctop.mm"
include "cuni.mm"
include "ctopon.mm"
include "mopntopon.mm"
include "3ad2ant1.mm"
include "topontop.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "elcls.mm"
include "mpbird.mm"
include "cpnf.mm"
include "cicc.mm"
include "metdsf.mm"
include "ffvelrnda.mm"
include "3impa.mm"
include "elxrge0.mm"
include "simplbi.mm"
include "xrleid.mm"
include "mpdan.mm"
include "syl5eq.mm"
include "simpll2.mm"
include "simplr.mm"
include "simpll3.mm"
include "blopn.mm"
include "simpr.mm"
include "xblcntr.mm"
include "syl112anc.mm"
include "clsndisj.mm"
include "syl32anc.mm"
include "ex.mm"
include "necon2bd.mm"
include "mpd.mm"
include "wo.mm"
include "simprbi.mm"
include "0xr.mm"
include "xrleloe.mm"
include "ord.mm"
include "eqcomd.mm"
include "impbida.mm"

theorem metdseq0
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cS: class S
  let cF: class F
  let cJ: class J
  let cX: class X
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let vs: setvar s
  let vt: setvar t
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cG: class G
  let cR: class R
  let cT: class T
  let cK: class K
  let cU: class U
  let cV: class V
  assume metdscn.f: |- F = ( x e. X |-> inf ( ran ( y e. S |-> ( x D y ) ) , RR* , < ) )
  assume metdscn.j: |- J = ( MetOpen ` D )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint D x
  disjoint D y
  disjoint J y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint r s
  disjoint r t
  disjoint D r
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint D s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint D t
  disjoint D w
  disjoint D z
  disjoint J r
  disjoint J s
  disjoint J t
  disjoint J w
  disjoint J z
  disjoint ph s
  disjoint ph t
  disjoint B x
  disjoint B y
  disjoint C r
  disjoint C s
  disjoint C w
  disjoint C z
  disjoint G s
  disjoint G t
  disjoint R w
  disjoint R z
  disjoint T s
  disjoint T t
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint K r
  disjoint K s
  disjoint K w
  disjoint K z
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S w
  disjoint S z
  disjoint U s
  disjoint U w
  disjoint X r
  disjoint X s
  disjoint X t
  disjoint X w
  disjoint X z
  disjoint F r
  disjoint F s
  disjoint F t
  disjoint F w
  disjoint F z
  disjoint V w
  disjoint V z
  assert |- ( ( D e. ( *Met ` X ) /\ S C_ X /\ A e. X ) -> ( ( F ` A ) = 0 <-> A e. ( ( cls ` J ) ` S ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cS
    cX
    wss
    #
    cA
    cX
    wcel
    #
    w3a
    #
    cA
    cF
    cfv
    #
    cc0
    wceq
    #
    cA
    cS
    cJ
    ccl
    cfv
    cfv
    wcel
    #
    @3
    @5
    wa
    #
    @6
    cA
    vz
    cv
    #
    wcel
    #
    @8
    cS
    cin
    #
    c0
    wne
    #
    wi
    #
    vz
    cJ
    wral
    #
    @7
    @12
    vz
    cJ
    @7
    @8
    cJ
    wcel
    #
    @9
    @11
    @7
    @14
    @9
    wa
    #
    wa
    #
    cA
    vr
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    @8
    wss
    #
    @11
    vr
    crp
    @16
    @0
    @14
    @9
    @20
    vr
    crp
    wrex
    @0
    @1
    @2
    @5
    @15
    simpll1
    #
    @7
    @14
    @9
    simprl
    @7
    @14
    @9
    simprr
    vr
    @8
    cD
    cA
    cJ
    cX
    metdscn.j
    mopni2
    syl3anc
    @16
    @17
    crp
    wcel
    #
    @20
    wa
    #
    wa
    #
    @19
    cS
    cin
    #
    @10
    wss
    #
    @25
    c0
    wne
    #
    @11
    @24
    @20
    @26
    @16
    @22
    @20
    simprr
    @19
    @8
    cS
    ssrin
    syl
    @24
    @17
    cc0
    cle
    wbr
    #
    wn
    #
    @27
    @22
    @29
    @16
    @20
    @22
    cc0
    @17
    clt
    wbr
    #
    @29
    @17
    rpgt0
    @22
    cc0
    cr
    wcel
    @17
    cr
    wcel
    @30
    @29
    wb
    0re
    @17
    rpre
    cc0
    @17
    ltnle
    sylancr
    mpbid
    ad2antrl
    @24
    @28
    @25
    c0
    @24
    @28
    cS
    @19
    cin
    #
    c0
    wceq
    #
    @25
    c0
    wceq
    @24
    @17
    @4
    cle
    wbr
    #
    @28
    @32
    @24
    @4
    cc0
    @17
    cle
    @3
    @5
    @15
    @23
    simpllr
    breq2d
    @24
    @0
    @1
    @2
    @17
    cxr
    wcel
    #
    @33
    @32
    wb
    @16
    @0
    @23
    @21
    adantr
    @7
    @1
    @15
    @23
    @0
    @1
    @2
    @5
    simpl2
    #
    ad2antrr
    @7
    @2
    @15
    @23
    @0
    @1
    @2
    @5
    simpl3
    #
    ad2antrr
    @22
    @34
    @16
    @20
    @17
    rpxr
    ad2antrl
    vx
    vy
    cA
    cD
    @17
    cS
    cF
    cX
    metdscn.f
    metdsge
    syl31anc
    bitr3d
    @31
    @25
    c0
    cS
    @19
    incom
    eqeq1i
    syl6bb
    necon3bbid
    mpbid
    @25
    @10
    ssn0
    syl2anc
    rexlimddv
    expr
    ralrimiva
    @7
    cJ
    ctop
    wcel
    #
    cS
    cJ
    cuni
    #
    wss
    #
    cA
    @38
    wcel
    @6
    @13
    wb
    @7
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @37
    @3
    @40
    @5
    @0
    @1
    @40
    @2
    cD
    cJ
    cX
    metdscn.j
    mopntopon
    3ad2ant1
    #
    adantr
    #
    cX
    cJ
    topontop
    #
    syl
    @7
    cS
    cX
    @38
    @35
    @7
    @40
    cX
    @38
    wceq
    #
    @42
    cX
    cJ
    toponuni
    #
    syl
    #
    sseqtrd
    @7
    cA
    cX
    @38
    @36
    @46
    eleqtrd
    vz
    cA
    cS
    cJ
    @38
    @38
    eqid
    #
    elcls
    syl3anc
    mpbird
    @3
    @6
    wa
    #
    cc0
    @4
    @48
    cc0
    @4
    clt
    wbr
    #
    wn
    #
    cc0
    @4
    wceq
    #
    @48
    cA
    @4
    @18
    co
    #
    cS
    cin
    #
    c0
    wceq
    #
    @50
    @3
    @54
    @6
    @3
    @53
    cS
    @52
    cin
    #
    c0
    @52
    cS
    incom
    @3
    @4
    @4
    cle
    wbr
    #
    @55
    c0
    wceq
    #
    @3
    @4
    cxr
    wcel
    #
    @56
    @3
    @4
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @58
    @0
    @1
    @2
    @60
    @0
    @1
    wa
    cX
    @59
    cA
    cF
    vx
    vy
    cD
    cS
    cF
    cX
    metdscn.f
    metdsf
    ffvelrnda
    3impa
    #
    @60
    @58
    cc0
    @4
    cle
    wbr
    #
    @4
    elxrge0
    #
    simplbi
    syl
    #
    @4
    xrleid
    syl
    @3
    @58
    @56
    @57
    wb
    @64
    vx
    vy
    cA
    cD
    @4
    cS
    cF
    cX
    metdscn.f
    metdsge
    mpdan
    mpbid
    syl5eq
    adantr
    @48
    @49
    @53
    c0
    @48
    @49
    @53
    c0
    wne
    #
    @48
    @49
    wa
    #
    @37
    @39
    @6
    @52
    cJ
    wcel
    #
    cA
    @52
    wcel
    #
    @65
    @66
    @40
    @37
    @3
    @40
    @6
    @49
    @41
    ad2antrr
    #
    @43
    syl
    @66
    cS
    cX
    @38
    @0
    @1
    @2
    @6
    @49
    simpll2
    @66
    @40
    @44
    @69
    @45
    syl
    sseqtrd
    @3
    @6
    @49
    simplr
    @66
    @0
    @2
    @58
    @67
    @0
    @1
    @2
    @6
    @49
    simpll1
    #
    @0
    @1
    @2
    @6
    @49
    simpll3
    #
    @3
    @58
    @6
    @49
    @64
    ad2antrr
    #
    cD
    cA
    @4
    cJ
    cX
    metdscn.j
    blopn
    syl3anc
    @66
    @0
    @2
    @58
    @49
    @68
    @70
    @71
    @72
    @48
    @49
    simpr
    cD
    cA
    @4
    cX
    xblcntr
    syl112anc
    cA
    cS
    @52
    cJ
    @38
    @47
    clsndisj
    syl32anc
    ex
    necon2bd
    mpd
    @48
    @49
    @51
    @3
    @49
    @51
    wo
    #
    @6
    @3
    @62
    @73
    @3
    @60
    @62
    @61
    @60
    @58
    @62
    @63
    simprbi
    syl
    @3
    cc0
    cxr
    wcel
    @58
    @62
    @73
    wb
    0xr
    @64
    cc0
    @4
    xrleloe
    sylancr
    mpbid
    adantr
    ord
    mpd
    eqcomd
    impbida
end
