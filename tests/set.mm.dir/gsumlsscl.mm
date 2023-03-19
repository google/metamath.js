include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cmap.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cvv.mm"
include "eqid.mm"
include "cabl.mm"
include "lmodabl.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "ssexg.mm"
include "ancoms.mm"
include "3adant1.mm"
include "csubg.mm"
include "3simpa.mm"
include "lsssubg.mm"
include "syl.mm"
include "wi.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "ex.mm"
include "ad2antrl.mm"
include "imp.mm"
include "ssel.mm"
include "3ad2ant3.mm"
include "lssvscl.mm"
include "syl12anc.mm"
include "fmptd.mm"
include "cbs.mm"
include "cpw.mm"
include "simp1.mm"
include "lssss.mm"
include "sstr.mm"
include "expcom.mm"
include "a1i.mm"
include "3imp.mm"
include "wb.mm"
include "elpwg.mm"
include "mpbird.mm"
include "jca.mm"
include "simprl.mm"
include "simprr.mm"
include "scmfsupp.mm"
include "syl3anc.mm"
include "gsumsubgcl.mm"

theorem gsumlsscl
  let vv: setvar v
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume gsumlsscl.s: |- S = ( LSubSp ` M )
  assume gsumlsscl.r: |- R = ( Scalar ` M )
  assume gsumlsscl.b: |- B = ( Base ` R )

  disjoint B v
  disjoint F v
  disjoint M v
  disjoint R v
  disjoint S v
  disjoint V v
  disjoint Z v
  disjoint k x
  assert |- ( ( M e. LMod /\ Z e. S /\ V C_ Z ) -> ( ( F e. ( B ^m V ) /\ F finSupp ( 0g ` R ) ) -> ( M gsum ( v e. V |-> ( ( F ` v ) ( .s ` M ) v ) ) ) e. Z ) )

  proof
    cM
    clmod
    wcel
    #
    cZ
    cS
    wcel
    #
    cV
    cZ
    wss
    #
    w3a
    #
    cF
    cB
    cV
    cmap
    co
    wcel
    #
    cF
    cR
    c0g
    cfv
    cfsupp
    wbr
    #
    wa
    #
    cM
    vv
    cV
    vv
    cv
    #
    cF
    cfv
    #
    @7
    cM
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    cZ
    wcel
    @3
    @6
    wa
    #
    cV
    cZ
    @11
    cM
    cvv
    cM
    c0g
    cfv
    #
    @13
    eqid
    @3
    cM
    cabl
    wcel
    #
    @6
    @0
    @1
    @14
    @2
    cM
    lmodabl
    3ad2ant1
    adantr
    @3
    cV
    cvv
    wcel
    #
    @6
    @1
    @2
    @15
    @0
    @2
    @1
    @15
    cV
    cZ
    cS
    ssexg
    ancoms
    3adant1
    #
    adantr
    @3
    cZ
    cM
    csubg
    cfv
    wcel
    #
    @6
    @3
    @0
    @1
    wa
    #
    @17
    @0
    @1
    @2
    3simpa
    #
    cS
    cZ
    cM
    gsumlsscl.s
    lsssubg
    syl
    adantr
    @12
    vv
    cV
    @10
    cZ
    @11
    @12
    @7
    cV
    wcel
    #
    wa
    @18
    @8
    cB
    wcel
    #
    @7
    cZ
    wcel
    #
    @10
    cZ
    wcel
    @12
    @18
    @20
    @3
    @18
    @6
    @19
    adantr
    adantr
    @12
    @20
    @21
    @4
    @20
    @21
    wi
    #
    @3
    @5
    @4
    cV
    cB
    cF
    wf
    #
    @23
    cF
    cB
    cV
    elmapi
    @24
    @20
    @21
    cV
    cB
    @7
    cF
    ffvelrn
    ex
    syl
    ad2antrl
    imp
    @12
    @20
    @22
    @3
    @20
    @22
    wi
    #
    @6
    @2
    @0
    @25
    @1
    cV
    cZ
    @7
    ssel
    3ad2ant3
    adantr
    imp
    cB
    cS
    @9
    cZ
    cR
    cM
    @8
    @7
    gsumlsscl.r
    @9
    eqid
    gsumlsscl.b
    gsumlsscl.s
    lssvscl
    syl12anc
    @11
    eqid
    fmptd
    @12
    @0
    cV
    cM
    cbs
    cfv
    #
    cpw
    wcel
    #
    wa
    #
    @4
    @5
    @11
    @13
    cfsupp
    wbr
    @3
    @28
    @6
    @3
    @0
    @27
    @0
    @1
    @2
    simp1
    @3
    @27
    cV
    @26
    wss
    #
    @0
    @1
    @2
    @29
    @1
    @2
    @29
    wi
    #
    wi
    @0
    @1
    cZ
    @26
    wss
    #
    @30
    cS
    cZ
    @26
    cM
    @26
    eqid
    gsumlsscl.s
    lssss
    @2
    @31
    @29
    cV
    cZ
    @26
    sstr
    expcom
    syl
    a1i
    3imp
    @3
    @15
    @27
    @29
    wb
    @16
    cV
    @26
    cvv
    elpwg
    syl
    mpbird
    jca
    adantr
    @3
    @4
    @5
    simprl
    @3
    @4
    @5
    simprr
    vv
    cF
    cB
    cR
    cM
    cV
    gsumlsscl.r
    gsumlsscl.b
    scmfsupp
    syl3anc
    gsumsubgcl
    ex
end
