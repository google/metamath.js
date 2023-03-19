include "wrel.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "alrimivv.mm"
include "eqrel.mm"
include "syl5ibr.mm"
include "imp.mm"

theorem eqrelrdv2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume eqrelrdv2.1: |- ( ph -> ( <. x , y >. e. A <-> <. x , y >. e. B ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ( ( Rel A /\ Rel B ) /\ ph ) -> A = B )

  proof
    cA
    wrel
    cB
    wrel
    wa
    #
    wph
    cA
    cB
    wceq
    #
    wph
    @1
    @0
    vx
    cv
    vy
    cv
    cop
    #
    cA
    wcel
    @2
    cB
    wcel
    wb
    #
    vy
    wal
    vx
    wal
    wph
    @3
    vx
    vy
    eqrelrdv2.1
    alrimivv
    vx
    vy
    cA
    cB
    eqrel
    syl5ibr
    imp
end
