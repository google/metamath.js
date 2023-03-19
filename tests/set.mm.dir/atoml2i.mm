include "cat.mm"
include "wcel.mm"
include "wss.mm"
include "wn.mm"
include "chj.mm"
include "co.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "cch.mm"
include "atelch.mm"
include "pjoml5.mm"
include "sylancr.mm"
include "incom.mm"
include "eqeq1i.mm"
include "biimpi.mm"
include "oveq2d.mm"
include "chj0i.mm"
include "syl6eq.mm"
include "sylan9req.mm"
include "ex.mm"
include "wb.mm"
include "chlejb2.mm"
include "sylancl.mm"
include "sylibrd.mm"
include "con3d.mm"
include "csn.mm"
include "cun.mm"
include "wo.mm"
include "atomli.mm"
include "elun.mm"
include "h0elch.mm"
include "elexi.mm"
include "elsn2.mm"
include "orbi2i.mm"
include "orcom.mm"
include "3bitri.mm"
include "sylib.mm"
include "ord.mm"
include "syld.mm"
include "imp.mm"

theorem atoml2i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let cC: class C
  assume atoml.1: |- A e. CH


  assert |- ( ( B e. HAtoms /\ -. B C_ A ) -> ( ( A vH B ) i^i ( _|_ ` A ) ) e. HAtoms )

  proof
    cB
    cat
    wcel
    #
    cB
    cA
    wss
    #
    wn
    #
    cA
    cB
    chj
    co
    #
    cA
    cort
    cfv
    #
    cin
    #
    cat
    wcel
    #
    @0
    @2
    @5
    c0h
    wceq
    #
    wn
    @6
    @0
    @7
    @1
    @0
    @7
    @3
    cA
    wceq
    #
    @1
    @0
    @7
    @8
    @0
    @7
    @3
    cA
    @4
    @3
    cin
    #
    chj
    co
    #
    cA
    @0
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    @10
    @3
    wceq
    atoml.1
    cB
    atelch
    #
    cA
    cB
    pjoml5
    sylancr
    @7
    @10
    cA
    c0h
    chj
    co
    cA
    @7
    @9
    c0h
    cA
    chj
    @7
    @9
    c0h
    wceq
    @5
    @9
    c0h
    @3
    @4
    incom
    eqeq1i
    biimpi
    oveq2d
    cA
    atoml.1
    chj0i
    syl6eq
    sylan9req
    ex
    @0
    @12
    @11
    @1
    @8
    wb
    @13
    atoml.1
    cB
    cA
    chlejb2
    sylancl
    sylibrd
    con3d
    @0
    @7
    @6
    @0
    @5
    cat
    c0h
    csn
    #
    cun
    wcel
    #
    @7
    @6
    wo
    #
    cA
    cB
    atoml.1
    atomli
    @15
    @6
    @5
    @14
    wcel
    #
    wo
    @6
    @7
    wo
    @16
    @5
    cat
    @14
    elun
    @17
    @7
    @6
    @5
    c0h
    c0h
    cch
    h0elch
    elexi
    elsn2
    orbi2i
    @6
    @7
    orcom
    3bitri
    sylib
    ord
    syld
    imp
end
