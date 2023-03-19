include "cab.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "ax-5.mm"
include "hbab1.mm"
include "cleqh.mm"
include "abid.mm"
include "bibi2i.mm"
include "albii.mm"
include "bitri.mm"

theorem abeq2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint ph y
  assert |- ( A = { x | ph } <-> A. x ( x e. A <-> ph ) )

  proof
    cA
    wph
    vx
    cab
    #
    wceq
    vx
    cv
    #
    cA
    wcel
    #
    @1
    @0
    wcel
    #
    wb
    #
    vx
    wal
    @2
    wph
    wb
    #
    vx
    wal
    vx
    vy
    cA
    @0
    vy
    cv
    cA
    wcel
    vx
    ax-5
    wph
    vx
    vy
    hbab1
    cleqh
    @4
    @5
    vx
    @3
    wph
    @2
    wph
    vx
    abid
    bibi2i
    albii
    bitri
end
