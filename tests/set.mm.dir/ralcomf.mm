include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "ancomst.mm"
include "2albii.mm"
include "alcom.mm"
include "bitri.mm"
include "r2alf.mm"
include "3bitr4i.mm"

theorem ralcomf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume ralcomf.1: |- F/_ y A
  assume ralcomf.2: |- F/_ x B

  disjoint x y
  assert |- ( A. x e. A A. y e. B ph <-> A. y e. B A. x e. A ph )

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
    wi
    #
    vy
    wal
    vx
    wal
    #
    @1
    @0
    wa
    wph
    wi
    #
    vx
    wal
    vy
    wal
    #
    wph
    vy
    cB
    wral
    vx
    cA
    wral
    wph
    vx
    cA
    wral
    vy
    cB
    wral
    @3
    @4
    vy
    wal
    vx
    wal
    @5
    @2
    @4
    vx
    vy
    @0
    @1
    wph
    ancomst
    2albii
    @4
    vx
    vy
    alcom
    bitri
    wph
    vx
    vy
    cA
    cB
    ralcomf.1
    r2alf
    wph
    vy
    vx
    cB
    cA
    ralcomf.2
    r2alf
    3bitr4i
end
