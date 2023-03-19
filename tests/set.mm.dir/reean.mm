include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "an4.mm"
include "2exbii.mm"
include "nfv.mm"
include "nfan.mm"
include "eean.mm"
include "bitri.mm"
include "r2ex.mm"
include "df-rex.mm"
include "anbi12i.mm"
include "3bitr4i.mm"

theorem reean
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume reean.1: |- F/ y ph
  assume reean.2: |- F/ x ps

  disjoint A y
  disjoint B x
  disjoint x y
  assert |- ( E. x e. A E. y e. B ( ph /\ ps ) <-> ( E. x e. A ph /\ E. y e. B ps ) )

  proof
    vx
    cv
    cA
    wcel
    #
    vy
    cv
    cB
    wcel
    #
    wa
    wph
    wps
    wa
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @0
    wph
    wa
    #
    vx
    wex
    #
    @1
    wps
    wa
    #
    vy
    wex
    #
    wa
    #
    @2
    vy
    cB
    wrex
    vx
    cA
    wrex
    wph
    vx
    cA
    wrex
    #
    wps
    vy
    cB
    wrex
    #
    wa
    @4
    @5
    @7
    wa
    #
    vy
    wex
    vx
    wex
    @9
    @3
    @12
    vx
    vy
    @0
    @1
    wph
    wps
    an4
    2exbii
    @5
    @7
    vx
    vy
    @0
    wph
    vy
    @0
    vy
    nfv
    reean.1
    nfan
    @1
    wps
    vx
    @1
    vx
    nfv
    reean.2
    nfan
    eean
    bitri
    @2
    vx
    vy
    cA
    cB
    r2ex
    @10
    @6
    @11
    @8
    wph
    vx
    cA
    df-rex
    wps
    vy
    cB
    df-rex
    anbi12i
    3bitr4i
end
