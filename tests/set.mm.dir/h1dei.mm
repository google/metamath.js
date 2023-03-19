include "csn.mm"
include "cort.mm"
include "cfv.mm"
include "wcel.mm"
include "chil.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wi.mm"
include "wss.mm"
include "wb.mm"
include "cch.mm"
include "snssi.mm"
include "occl.mm"
include "mp2b.mm"
include "chssii.mm"
include "ocel.mm"
include "ax-mp.mm"
include "h1deoi.mm"
include "orthcom.mm"
include "mpan2.mm"
include "pm5.32i.mm"
include "bitri.mm"
include "imbi1i.mm"
include "impexp.mm"
include "ralbii2.mm"
include "anbi2i.mm"

theorem h1dei
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume h1deot.1: |- B e. ~H

  disjoint A x
  disjoint B x
  assert |- ( A e. ( _|_ ` ( _|_ ` { B } ) ) <-> ( A e. ~H /\ A. x e. ~H ( ( B .ih x ) = 0 -> ( A .ih x ) = 0 ) ) )

  proof
    cA
    cB
    csn
    #
    cort
    cfv
    #
    cort
    cfv
    wcel
    #
    cA
    chil
    wcel
    #
    cA
    vx
    cv
    #
    csp
    co
    cc0
    wceq
    #
    vx
    @1
    wral
    #
    wa
    #
    @3
    cB
    @4
    csp
    co
    cc0
    wceq
    #
    @5
    wi
    #
    vx
    chil
    wral
    #
    wa
    @1
    chil
    wss
    @2
    @7
    wb
    @1
    cB
    chil
    wcel
    #
    @0
    chil
    wss
    @1
    cch
    wcel
    h1deot.1
    cB
    chil
    snssi
    @0
    occl
    mp2b
    chssii
    vx
    cA
    @1
    ocel
    ax-mp
    @6
    @10
    @3
    @5
    @9
    vx
    @1
    chil
    @4
    @1
    wcel
    #
    @5
    wi
    @4
    chil
    wcel
    #
    @8
    wa
    #
    @5
    wi
    @13
    @9
    wi
    @12
    @14
    @5
    @12
    @13
    @4
    cB
    csp
    co
    cc0
    wceq
    #
    wa
    @14
    @4
    cB
    h1deot.1
    h1deoi
    @13
    @15
    @8
    @13
    @11
    @15
    @8
    wb
    h1deot.1
    @4
    cB
    orthcom
    mpan2
    pm5.32i
    bitri
    imbi1i
    @13
    @8
    @5
    impexp
    bitri
    ralbii2
    anbi2i
    bitri
end
