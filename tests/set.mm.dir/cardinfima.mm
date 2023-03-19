include "wcel.mm"
include "cvv.mm"
include "com.mm"
include "cale.mm"
include "crn.mm"
include "cun.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wrex.mm"
include "wa.mm"
include "cima.mm"
include "cuni.mm"
include "wi.mm"
include "elex.mm"
include "wss.mm"
include "ccrd.mm"
include "wceq.mm"
include "isinfcard.mm"
include "bicomi.mm"
include "simplbi.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "ex.mm"
include "fnima.mm"
include "eleq2d.mm"
include "sylibrd.mm"
include "elssuni.mm"
include "syl6.mm"
include "imp.mm"
include "sylan.mm"
include "sylan9ssr.mm"
include "anasss.mm"
include "a1i.mm"
include "carduniima.mm"
include "iscard3.mm"
include "syl6ibr.mm"
include "adantrd.mm"
include "jcad.mm"
include "syl6ib.mm"
include "exp4d.mm"
include "rexlimdv.mm"
include "expimpd.mm"
include "syl.mm"

theorem cardinfima
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint F x
  disjoint A x
  assert |- ( A e. B -> ( ( F : A --> ( _om u. ran aleph ) /\ E. x e. A ( F ` x ) e. ran aleph ) -> U. ( F " A ) e. ran aleph ) )

  proof
    cA
    cB
    wcel
    cA
    cvv
    wcel
    #
    cA
    com
    cale
    crn
    #
    cun
    #
    cF
    wf
    #
    vx
    cv
    #
    cF
    cfv
    #
    @1
    wcel
    #
    vx
    cA
    wrex
    #
    wa
    cF
    cA
    cima
    #
    cuni
    #
    @1
    wcel
    #
    wi
    cA
    cB
    elex
    @0
    @3
    @7
    @10
    @0
    @3
    wa
    @6
    @10
    vx
    cA
    @0
    @3
    @4
    cA
    wcel
    #
    @6
    @10
    wi
    wi
    @0
    @3
    @11
    @6
    @10
    @0
    @3
    @11
    @6
    wa
    #
    wa
    #
    com
    @9
    wss
    #
    @9
    ccrd
    cfv
    @9
    wceq
    #
    wa
    @10
    @0
    @13
    @14
    @15
    @13
    @14
    wi
    @0
    @3
    @11
    @6
    @14
    @6
    @3
    @11
    wa
    com
    @5
    @9
    @6
    com
    @5
    wss
    #
    @5
    ccrd
    cfv
    @5
    wceq
    #
    @16
    @17
    wa
    @6
    @5
    isinfcard
    bicomi
    simplbi
    @3
    cF
    cA
    wfn
    #
    @11
    @5
    @9
    wss
    #
    cA
    @2
    cF
    ffn
    @18
    @11
    @19
    @18
    @11
    @5
    @8
    wcel
    #
    @19
    @18
    @11
    @5
    cF
    crn
    #
    wcel
    #
    @20
    @18
    @11
    @22
    cA
    @4
    cF
    fnfvelrn
    ex
    @18
    @8
    @21
    @5
    cA
    cF
    fnima
    eleq2d
    sylibrd
    @5
    @8
    elssuni
    syl6
    imp
    sylan
    sylan9ssr
    anasss
    a1i
    @0
    @3
    @15
    @12
    @0
    @3
    @9
    @2
    wcel
    @15
    cA
    cvv
    cF
    carduniima
    @9
    iscard3
    syl6ibr
    adantrd
    jcad
    @9
    isinfcard
    syl6ib
    exp4d
    imp
    rexlimdv
    expimpd
    syl
end
