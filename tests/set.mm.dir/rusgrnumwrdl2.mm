include "crusgr.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cedg.mm"
include "w3a.mm"
include "cword.mm"
include "crab.mm"
include "cvv.mm"
include "wf1o.mm"
include "wex.mm"
include "cvtx.mm"
include "fvex.mm"
include "eqeltri.mm"
include "wrdexi.mm"
include "rabex.mm"
include "a1i.mm"
include "wrd2f1tovbij.mm"
include "sylan.mm"
include "hasheqf1oi.mm"
include "mpsyl.mm"
include "cusgr.mm"
include "cxnn0.mm"
include "wral.mm"
include "wi.mm"
include "rusgrpropadjvtx.mm"
include "preq1.mm"
include "eleq1d.mm"
include "rabbidv.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "rspccv.mm"
include "3ad2ant3.mm"
include "syl.mm"
include "imp.mm"
include "eqtrd.mm"

theorem rusgrnumwrdl2
  let vw: setvar w
  let cP: class P
  let cG: class G
  let cK: class K
  let cV: class V
  let vf: setvar f
  let vp: setvar p
  let vs: setvar s
  assume rusgrnumwrdl2.v: |- V = ( Vtx ` G )

  disjoint G w
  disjoint P w
  disjoint V w
  disjoint G f
  disjoint G p
  disjoint G s
  disjoint f p
  disjoint f s
  disjoint f w
  disjoint p s
  disjoint p w
  disjoint s w
  disjoint K p
  disjoint P f
  disjoint P p
  disjoint P s
  disjoint V f
  disjoint V p
  disjoint V s
  assert |- ( ( G RegUSGraph K /\ P e. V ) -> ( # ` { w e. Word V | ( ( # ` w ) = 2 /\ ( w ` 0 ) = P /\ { ( w ` 0 ) , ( w ` 1 ) } e. ( Edg ` G ) ) } ) = K )

  proof
    cG
    cK
    crusgr
    wbr
    #
    cP
    cV
    wcel
    #
    wa
    #
    vw
    cv
    #
    chash
    cfv
    c2
    wceq
    cc0
    @3
    cfv
    #
    cP
    wceq
    @4
    c1
    @3
    cfv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    w3a
    #
    vw
    cV
    cword
    #
    crab
    #
    chash
    cfv
    #
    cP
    vs
    cv
    #
    cpr
    #
    @5
    wcel
    #
    vs
    cV
    crab
    #
    chash
    cfv
    #
    cK
    @8
    cvv
    wcel
    @2
    @8
    @13
    vf
    cv
    wf1o
    vf
    wex
    #
    @9
    @14
    wceq
    @6
    vw
    @7
    cV
    cV
    cG
    cvtx
    cfv
    cvv
    rusgrnumwrdl2.v
    cG
    cvtx
    fvex
    eqeltri
    #
    wrdexi
    rabex
    @0
    cV
    cvv
    wcel
    #
    @1
    @15
    @17
    @0
    @16
    a1i
    vw
    cP
    vf
    vs
    cV
    @5
    cvv
    wrd2f1tovbij
    sylan
    @8
    @13
    vf
    cvv
    hasheqf1oi
    mpsyl
    @0
    @1
    @14
    cK
    wceq
    #
    @0
    cG
    cusgr
    wcel
    #
    cK
    cxnn0
    wcel
    #
    vp
    cv
    #
    @10
    cpr
    #
    @5
    wcel
    #
    vs
    cV
    crab
    #
    chash
    cfv
    #
    cK
    wceq
    #
    vp
    cV
    wral
    #
    w3a
    @1
    @18
    wi
    #
    vp
    vs
    cG
    cK
    cV
    rusgrnumwrdl2.v
    rusgrpropadjvtx
    @27
    @19
    @28
    @20
    @26
    @18
    vp
    cP
    cV
    @21
    cP
    wceq
    #
    @25
    @14
    cK
    @29
    @24
    @13
    chash
    @29
    @23
    @12
    vs
    cV
    @29
    @22
    @11
    @5
    @21
    cP
    @10
    preq1
    eleq1d
    rabbidv
    fveq2d
    eqeq1d
    rspccv
    3ad2ant3
    syl
    imp
    eqtrd
end
