include "cv.mm"
include "wcel.mm"
include "wal.mm"
include "wi.mm"
include "wral.mm"
include "19.21v.mm"
include "bicomi.mm"
include "albii.mm"
include "alcom.mm"
include "bitri.mm"
include "df-ral.mm"
include "3bitr4i.mm"

theorem bj-ralcom4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A y
  assert |- ( A. x e. A A. y ph <-> A. y A. x e. A ph )

  proof
    vx
    cv
    cA
    wcel
    #
    wph
    vy
    wal
    #
    wi
    #
    vx
    wal
    #
    @0
    wph
    wi
    #
    vx
    wal
    #
    vy
    wal
    #
    @1
    vx
    cA
    wral
    wph
    vx
    cA
    wral
    #
    vy
    wal
    @3
    @4
    vy
    wal
    #
    vx
    wal
    @6
    @2
    @8
    vx
    @8
    @2
    @0
    wph
    vy
    19.21v
    bicomi
    albii
    @4
    vx
    vy
    alcom
    bitri
    @1
    vx
    cA
    df-ral
    @7
    @5
    vy
    wph
    vx
    cA
    df-ral
    albii
    3bitr4i
end
