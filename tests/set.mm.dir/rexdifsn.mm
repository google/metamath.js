include "cv.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "eldifsn.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "rexbii2.mm"

theorem rexdifsn
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( E. x e. ( A \ { B } ) ph <-> E. x e. A ( x =/= B /\ ph ) )

  proof
    wph
    vx
    cv
    #
    cB
    wne
    #
    wph
    wa
    #
    vx
    cA
    cB
    csn
    cdif
    #
    cA
    @0
    @3
    wcel
    #
    wph
    wa
    @0
    cA
    wcel
    #
    @1
    wa
    #
    wph
    wa
    @5
    @2
    wa
    @4
    @6
    wph
    @0
    cA
    cB
    eldifsn
    anbi1i
    @5
    @1
    wph
    anass
    bitri
    rexbii2
end
