include "wex.mm"
include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "df-rex.mm"
include "19.42v.mm"
include "bicomi.mm"
include "exbii.mm"
include "excom.mm"
include "bitri.mm"

theorem bj-rexcom4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A y
  assert |- ( E. x e. A E. y ph <-> E. y E. x e. A ph )

  proof
    wph
    vy
    wex
    #
    vx
    cA
    wrex
    vx
    cv
    cA
    wcel
    #
    @0
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
    vy
    wex
    #
    @0
    vx
    cA
    df-rex
    @3
    @1
    wph
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    @5
    @2
    @7
    vx
    @7
    @2
    @1
    wph
    vy
    19.42v
    bicomi
    exbii
    @8
    @6
    vx
    wex
    #
    vy
    wex
    @5
    @6
    vx
    vy
    excom
    @9
    @4
    vy
    @4
    @9
    wph
    vx
    cA
    df-rex
    bicomi
    exbii
    bitri
    bitri
    bitri
end
