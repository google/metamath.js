include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wne.mm"
include "anass.mm"
include "eldifsn.mm"
include "anbi1i.mm"
include "ne0i.mm"
include "pm4.71ri.mm"
include "bitri.mm"
include "anbi2i.mm"
include "3bitr4ri.mm"
include "rexbii2.mm"

theorem prtlem100
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( E. x e. A ( B e. x /\ ph ) <-> E. x e. ( A \ { (/) } ) ( B e. x /\ ph ) )

  proof
    cB
    vx
    cv
    #
    wcel
    #
    wph
    wa
    #
    @2
    vx
    cA
    cA
    c0
    csn
    cdif
    #
    @0
    cA
    wcel
    #
    @0
    c0
    wne
    #
    wa
    #
    @2
    wa
    @4
    @5
    @2
    wa
    #
    wa
    @0
    @3
    wcel
    #
    @2
    wa
    @4
    @2
    wa
    @4
    @5
    @2
    anass
    @8
    @6
    @2
    @0
    cA
    c0
    eldifsn
    anbi1i
    @2
    @7
    @4
    @2
    @5
    @1
    wa
    #
    wph
    wa
    @7
    @1
    @9
    wph
    @1
    @5
    @0
    cB
    ne0i
    pm4.71ri
    anbi1i
    @5
    @1
    wph
    anass
    bitri
    anbi2i
    3bitr4ri
    rexbii2
end
