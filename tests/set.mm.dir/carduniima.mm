include "wcel.mm"
include "com.mm"
include "cale.mm"
include "crn.mm"
include "cun.mm"
include "wf.mm"
include "cima.mm"
include "cuni.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "cvv.mm"
include "wfun.mm"
include "ffun.mm"
include "funimaexg.mm"
include "sylan.mm"
include "expcom.mm"
include "cv.mm"
include "wral.mm"
include "wfn.mm"
include "ffn.mm"
include "fnima.mm"
include "syl.mm"
include "frn.mm"
include "eqsstrd.mm"
include "sseld.mm"
include "iscard3.mm"
include "syl6ibr.mm"
include "ralrimiv.mm"
include "carduni.mm"
include "syl5.mm"
include "syli.mm"
include "syl6ib.mm"

theorem carduniima
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x


  assert |- ( A e. B -> ( F : A --> ( _om u. ran aleph ) -> U. ( F " A ) e. ( _om u. ran aleph ) ) )

  proof
    cA
    cB
    wcel
    #
    cA
    com
    cale
    crn
    cun
    #
    cF
    wf
    #
    cF
    cA
    cima
    #
    cuni
    #
    ccrd
    cfv
    @4
    wceq
    #
    @4
    @1
    wcel
    @2
    @0
    @3
    cvv
    wcel
    #
    @5
    @2
    @0
    @6
    @2
    cF
    wfun
    @0
    @6
    cA
    @1
    cF
    ffun
    cF
    cA
    cB
    funimaexg
    sylan
    expcom
    @2
    vx
    cv
    #
    ccrd
    cfv
    @7
    wceq
    #
    vx
    @3
    wral
    @6
    @5
    @2
    @8
    vx
    @3
    @2
    @7
    @3
    wcel
    @7
    @1
    wcel
    @8
    @2
    @3
    @1
    @7
    @2
    @3
    cF
    crn
    #
    @1
    @2
    cF
    cA
    wfn
    @3
    @9
    wceq
    cA
    @1
    cF
    ffn
    cA
    cF
    fnima
    syl
    cA
    @1
    cF
    frn
    eqsstrd
    sseld
    @7
    iscard3
    syl6ibr
    ralrimiv
    vx
    @3
    cvv
    carduni
    syl5
    syli
    @4
    iscard3
    syl6ib
end
