include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wceq.mm"
include "alrimivv.mm"
include "wrel.mm"
include "eqrel.mm"
include "mp2an.mm"
include "sylibr.mm"

theorem eqrelrdv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume eqrelrdv.1: |- Rel A
  assume eqrelrdv.2: |- Rel B
  assume eqrelrdv.3: |- ( ph -> ( <. x , y >. e. A <-> <. x , y >. e. B ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> A = B )

  proof
    wph
    vx
    cv
    vy
    cv
    cop
    #
    cA
    wcel
    @0
    cB
    wcel
    wb
    #
    vy
    wal
    vx
    wal
    #
    cA
    cB
    wceq
    #
    wph
    @1
    vx
    vy
    eqrelrdv.3
    alrimivv
    cA
    wrel
    cB
    wrel
    @3
    @2
    wb
    eqrelrdv.1
    eqrelrdv.2
    vx
    vy
    cA
    cB
    eqrel
    mp2an
    sylibr
end
