include "cun.mm"
include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wo.mm"
include "df-rex.mm"
include "19.43.mm"
include "elun.mm"
include "anbi1i.mm"
include "andir.mm"
include "bitri.mm"
include "exbii.mm"
include "orbi12i.mm"
include "3bitr4i.mm"

theorem rexun
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( E. x e. ( A u. B ) ph <-> ( E. x e. A ph \/ E. x e. B ph ) )

  proof
    wph
    vx
    cA
    cB
    cun
    #
    wrex
    vx
    cv
    #
    @0
    wcel
    #
    wph
    wa
    #
    vx
    wex
    #
    wph
    vx
    cA
    wrex
    #
    wph
    vx
    cB
    wrex
    #
    wo
    #
    wph
    vx
    @0
    df-rex
    @1
    cA
    wcel
    #
    wph
    wa
    #
    @1
    cB
    wcel
    #
    wph
    wa
    #
    wo
    #
    vx
    wex
    @9
    vx
    wex
    #
    @11
    vx
    wex
    #
    wo
    @4
    @7
    @9
    @11
    vx
    19.43
    @3
    @12
    vx
    @3
    @8
    @10
    wo
    #
    wph
    wa
    @12
    @2
    @15
    wph
    @1
    cA
    cB
    elun
    anbi1i
    @8
    @10
    wph
    andir
    bitri
    exbii
    @5
    @13
    @6
    @14
    wph
    vx
    cA
    df-rex
    wph
    vx
    cB
    df-rex
    orbi12i
    3bitr4i
    bitri
end
