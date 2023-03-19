include "wal.mm"
include "cab.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "df-clel.mm"
include "a1i.mm"
include "bj-vexwvt.mm"
include "biantrud.mm"
include "bicomd.mm"
include "exbidv.mm"
include "bj-denotes.mm"
include "3bitrd.mm"

theorem bj-issetwt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint A y
  disjoint x z
  disjoint A z
  disjoint ph z
  assert |- ( A. x ph -> ( A e. { x | ph } <-> E. y y = A ) )

  proof
    wph
    vx
    wal
    #
    cA
    wph
    vx
    cab
    #
    wcel
    #
    vz
    cv
    #
    cA
    wceq
    #
    @3
    @1
    wcel
    #
    wa
    #
    vz
    wex
    #
    @4
    vz
    wex
    #
    vy
    cv
    cA
    wceq
    vy
    wex
    #
    @2
    @7
    wb
    @0
    vz
    cA
    @1
    df-clel
    a1i
    @0
    @6
    @4
    vz
    @0
    @4
    @6
    @0
    @5
    @4
    wph
    vx
    vz
    bj-vexwvt
    biantrud
    bicomd
    exbidv
    @8
    @9
    wb
    @0
    vz
    vy
    cA
    bj-denotes
    a1i
    3bitrd
end
