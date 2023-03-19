include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "cort.mm"
include "cfv.mm"
include "cch.mm"
include "c0h.mm"
include "cv.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "cat.mm"
include "snssi.mm"
include "occl.mm"
include "choccl.mm"
include "3syl.mm"
include "adantr.mm"
include "h1dn0.mm"
include "h1datom.mm"
include "expcom.mm"
include "ralrimiv.mm"
include "jca.mm"
include "elat2.mm"
include "sylanbrc.mm"

theorem h1da
  let cA: class A
  let vx: setvar x


  assert |- ( ( A e. ~H /\ A =/= 0h ) -> ( _|_ ` ( _|_ ` { A } ) ) e. HAtoms )

  proof
    cA
    chil
    wcel
    #
    cA
    c0v
    wne
    #
    wa
    #
    cA
    csn
    #
    cort
    cfv
    #
    cort
    cfv
    #
    cch
    wcel
    #
    @5
    c0h
    wne
    #
    vx
    cv
    #
    @5
    wss
    @8
    @5
    wceq
    @8
    c0h
    wceq
    wo
    wi
    #
    vx
    cch
    wral
    #
    wa
    @5
    cat
    wcel
    @0
    @6
    @1
    @0
    @3
    chil
    wss
    @4
    cch
    wcel
    @6
    cA
    chil
    snssi
    @3
    occl
    @4
    choccl
    3syl
    adantr
    @2
    @7
    @10
    cA
    h1dn0
    @0
    @10
    @1
    @0
    @9
    vx
    cch
    @8
    cch
    wcel
    @0
    @9
    @8
    cA
    h1datom
    expcom
    ralrimiv
    adantr
    jca
    vx
    @5
    elat2
    sylanbrc
end
