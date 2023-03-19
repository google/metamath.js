include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "hbim.mm"
include "hbal.mm"
include "hbxfrbi.mm"

theorem hbral
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume hbral.1: |- ( y e. A -> A. x y e. A )
  assume hbral.2: |- ( ph -> A. x ph )


  assert |- ( A. y e. A ph -> A. x A. y e. A ph )

  proof
    wph
    vy
    cA
    wral
    vy
    cv
    cA
    wcel
    #
    wph
    wi
    #
    vy
    wal
    vx
    wph
    vy
    cA
    df-ral
    @1
    vx
    vy
    @0
    wph
    vx
    hbral.1
    hbral.2
    hbim
    hbal
    hbxfrbi
end
