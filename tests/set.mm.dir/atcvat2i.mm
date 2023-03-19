include "cat.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wn.mm"
include "chj.mm"
include "co.mm"
include "ccv.mm"
include "wbr.mm"
include "wi.mm"
include "c0h.mm"
include "wne.mm"
include "cch.mm"
include "wb.mm"
include "atcv1.mm"
include "mp3anl1.mm"
include "necon3abid.mm"
include "wpss.mm"
include "atelch.mm"
include "chjcl.mm"
include "syl2an.mm"
include "cvpss.mm"
include "sylancr.mm"
include "atcvati.mm"
include "expcomd.mm"
include "syld.mm"
include "imp.mm"
include "sylbird.mm"
include "ex.mm"
include "com23.mm"
include "impd.mm"

theorem atcvat2i
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  assume atoml.1: |- A e. CH


  assert |- ( ( B e. HAtoms /\ C e. HAtoms ) -> ( ( -. B = C /\ A <oH ( B vH C ) ) -> A e. HAtoms ) )

  proof
    cB
    cat
    wcel
    #
    cC
    cat
    wcel
    #
    wa
    #
    cB
    cC
    wceq
    #
    wn
    #
    cA
    cB
    cC
    chj
    co
    #
    ccv
    wbr
    #
    cA
    cat
    wcel
    #
    @2
    @6
    @4
    @7
    @2
    @6
    @4
    @7
    wi
    @2
    @6
    wa
    #
    @4
    cA
    c0h
    wne
    #
    @7
    @8
    @3
    cA
    c0h
    cA
    cch
    wcel
    #
    @0
    @1
    @6
    cA
    c0h
    wceq
    @3
    wb
    atoml.1
    cA
    cB
    cC
    atcv1
    mp3anl1
    necon3abid
    @2
    @6
    @9
    @7
    wi
    #
    @2
    @6
    cA
    @5
    wpss
    #
    @11
    @2
    @10
    @5
    cch
    wcel
    #
    @6
    @12
    wi
    atoml.1
    @0
    cB
    cch
    wcel
    cC
    cch
    wcel
    @13
    @1
    cB
    atelch
    cC
    atelch
    cB
    cC
    chjcl
    syl2an
    cA
    @5
    cvpss
    sylancr
    @2
    @9
    @12
    @7
    cA
    cB
    cC
    atoml.1
    atcvati
    expcomd
    syld
    imp
    sylbird
    ex
    com23
    impd
end
