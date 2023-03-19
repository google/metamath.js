include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "csca.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "clinc.mm"
include "cplusg.mm"
include "eqid.mm"
include "simp1l.mm"
include "simpr.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "wi.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "ex.mm"
include "syl.mm"
include "imp.mm"
include "elelpwi.mm"
include "expcom.mm"
include "adantl.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "scmfsupp.mm"
include "3adant2r.mm"
include "gsumvsmul.mm"
include "wceq.mm"
include "crg.mm"
include "lmodring.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "syl6eleq.mm"
include "ringcl.mm"
include "fmptd.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"
include "lincval.mm"
include "ovex.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "lmodvsass.mm"
include "syl13anc.mm"
include "eqcomi.mm"
include "a1i.mm"
include "oveqd.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "oveq1i.mm"
include "3eqtr4rd.mm"

theorem lincscm
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cM: class M
  let cV: class V
  let cX: class X
  let vv: setvar v
  let vk: setvar k
  assume lincscm.s: |- .xb = ( .s ` M )
  assume lincscm.t: |- .x. = ( .r ` ( Scalar ` M ) )
  assume lincscm.x: |- X = ( A ( linC ` M ) V )
  assume lincscm.r: |- R = ( Base ` ( Scalar ` M ) )
  assume lincscm.f: |- F = ( x e. V |-> ( S .x. ( A ` x ) ) )

  disjoint A x
  disjoint M x
  disjoint R x
  disjoint S x
  disjoint V x
  disjoint .x. x
  disjoint A v
  disjoint v x
  disjoint F v
  disjoint M v
  disjoint R v
  disjoint S v
  disjoint V v
  disjoint .xb v
  disjoint .x. v
  disjoint k x
  assert |- ( ( ( M e. LMod /\ V e. ~P ( Base ` M ) ) /\ ( A e. ( R ^m V ) /\ S e. R ) /\ A finSupp ( 0g ` ( Scalar ` M ) ) ) -> ( S .xb X ) = ( F ( linC ` M ) V ) )

  proof
    cM
    clmod
    wcel
    #
    cV
    cM
    cbs
    cfv
    #
    cpw
    #
    wcel
    #
    wa
    #
    cA
    cR
    cV
    cmap
    co
    #
    wcel
    #
    cS
    cR
    wcel
    #
    wa
    #
    cA
    cM
    csca
    cfv
    #
    c0g
    cfv
    cfsupp
    wbr
    #
    w3a
    #
    cM
    vv
    cV
    cS
    vv
    cv
    #
    cA
    cfv
    #
    @12
    cM
    cvsca
    cfv
    #
    co
    #
    c.xb
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cS
    cM
    vv
    cV
    @15
    cmpt
    #
    cgsu
    co
    #
    c.xb
    co
    cF
    cV
    cM
    clinc
    cfv
    #
    co
    #
    cS
    cX
    c.xb
    co
    @11
    cV
    @1
    cM
    cplusg
    cfv
    #
    cM
    @9
    c.xb
    vv
    cR
    @2
    cS
    @15
    cM
    c0g
    cfv
    #
    @1
    eqid
    #
    @9
    eqid
    #
    lincscm.r
    @24
    eqid
    @23
    eqid
    lincscm.s
    @0
    @3
    @8
    @10
    simp1l
    #
    @4
    @8
    @3
    @10
    @0
    @3
    simpr
    3ad2ant1
    #
    @8
    @4
    @7
    @10
    @6
    @7
    simpr
    3ad2ant2
    #
    @11
    @12
    cV
    wcel
    #
    wa
    #
    @0
    @13
    cR
    wcel
    #
    @12
    @1
    wcel
    #
    @15
    @1
    wcel
    @11
    @0
    @30
    @27
    adantr
    #
    @11
    @30
    @32
    @8
    @4
    @30
    @32
    wi
    #
    @10
    @6
    @35
    @7
    @6
    cV
    cR
    cA
    wf
    #
    @35
    cA
    cR
    cV
    elmapi
    #
    @36
    @30
    @32
    cV
    cR
    @12
    cA
    ffvelrn
    ex
    syl
    adantr
    3ad2ant2
    imp
    #
    @11
    @30
    @33
    @4
    @8
    @30
    @33
    wi
    #
    @10
    @3
    @39
    @0
    @30
    @3
    @33
    @12
    cV
    @1
    elelpwi
    expcom
    adantl
    3ad2ant1
    imp
    #
    @13
    @14
    @9
    cR
    @1
    cM
    @12
    @25
    @26
    @14
    eqid
    #
    lincscm.r
    lmodvscl
    syl3anc
    @4
    @6
    @10
    @19
    @24
    cfsupp
    wbr
    @7
    vv
    cA
    cR
    @9
    cM
    cV
    @26
    lincscm.r
    scmfsupp
    3adant2r
    gsumvsmul
    @11
    @22
    cM
    vv
    cV
    @12
    cF
    cfv
    #
    @12
    @14
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @18
    @11
    @0
    cF
    @9
    cbs
    cfv
    #
    cV
    cmap
    co
    #
    wcel
    #
    @3
    @22
    @45
    wceq
    @27
    @11
    @48
    cV
    @46
    cF
    wf
    #
    @11
    vx
    cV
    cS
    vx
    cv
    #
    cA
    cfv
    #
    c.x
    co
    #
    @46
    cF
    @11
    @50
    cV
    wcel
    #
    wa
    @9
    crg
    wcel
    #
    cS
    @46
    wcel
    #
    @51
    @46
    wcel
    #
    @52
    @46
    wcel
    @11
    @54
    @53
    @4
    @8
    @54
    @10
    @0
    @54
    @3
    @9
    cM
    @26
    lmodring
    adantr
    3ad2ant1
    adantr
    @11
    @55
    @53
    @8
    @4
    @55
    @10
    @7
    @55
    @6
    @7
    @55
    cR
    @46
    cS
    lincscm.r
    eleq2i
    biimpi
    adantl
    3ad2ant2
    adantr
    @11
    @53
    @56
    @8
    @4
    @53
    @56
    wi
    #
    @10
    @6
    @57
    @7
    @6
    @36
    @57
    @37
    @36
    @53
    @56
    @36
    @53
    wa
    @51
    cR
    @46
    cV
    cR
    @50
    cA
    ffvelrn
    lincscm.r
    syl6eleq
    ex
    syl
    adantr
    3ad2ant2
    imp
    @46
    @9
    c.x
    cS
    @51
    @46
    eqid
    lincscm.t
    ringcl
    syl3anc
    lincscm.f
    fmptd
    @11
    @46
    cvv
    wcel
    @3
    @48
    @49
    wb
    @9
    cbs
    fvex
    @28
    @46
    cV
    cF
    cvv
    @2
    elmapg
    sylancr
    mpbird
    @28
    vv
    cF
    cM
    cV
    clmod
    lincval
    syl3anc
    @11
    @44
    @17
    cM
    cgsu
    @11
    vv
    cV
    @43
    @16
    @31
    @43
    cS
    @13
    c.x
    co
    #
    @12
    @14
    co
    #
    @16
    @31
    @42
    @58
    @12
    @14
    @31
    @30
    @58
    cvv
    wcel
    @42
    @58
    wceq
    @11
    @30
    simpr
    cS
    @13
    c.x
    ovex
    vx
    @12
    @52
    @58
    cV
    cvv
    cF
    @50
    @12
    wceq
    @51
    @13
    cS
    c.x
    @50
    @12
    cA
    fveq2
    oveq2d
    lincscm.f
    fvmptg
    sylancl
    oveq1d
    @31
    @59
    cS
    @15
    @14
    co
    #
    @16
    @31
    @0
    @7
    @32
    @33
    @59
    @60
    wceq
    @34
    @11
    @7
    @30
    @29
    adantr
    @38
    @40
    cS
    @13
    @14
    c.x
    @9
    cR
    @1
    cM
    @12
    @25
    @26
    @41
    lincscm.r
    lincscm.t
    lmodvsass
    syl13anc
    @31
    @14
    c.xb
    cS
    @15
    @14
    c.xb
    wceq
    @31
    c.xb
    @14
    lincscm.s
    eqcomi
    a1i
    oveqd
    eqtrd
    eqtrd
    mpteq2dva
    oveq2d
    eqtrd
    @11
    cX
    @20
    cS
    c.xb
    @11
    cX
    cA
    cV
    @21
    co
    #
    @20
    cX
    @61
    wceq
    @11
    lincscm.x
    a1i
    @11
    @0
    cA
    @47
    wcel
    #
    @3
    @61
    @20
    wceq
    @27
    @8
    @4
    @62
    @10
    @6
    @62
    @7
    @6
    @62
    @5
    @47
    cA
    cR
    @46
    cV
    cmap
    lincscm.r
    oveq1i
    eleq2i
    biimpi
    adantr
    3ad2ant2
    @28
    vv
    cA
    cM
    cV
    clmod
    lincval
    syl3anc
    eqtrd
    oveq2d
    3eqtr4rd
end
