include "wss.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "alrimivv.mm"
include "wrel.mm"
include "wb.mm"
include "ssrel.mm"
include "syl.mm"
include "mpbird.mm"

theorem relssdv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume relssdv.1: |- ( ph -> Rel A )
  assume relssdv.2: |- ( ph -> ( <. x , y >. e. A -> <. x , y >. e. B ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> A C_ B )

  proof
    wph
    cA
    cB
    wss
    #
    vx
    cv
    vy
    cv
    cop
    #
    cA
    wcel
    @1
    cB
    wcel
    wi
    #
    vy
    wal
    vx
    wal
    #
    wph
    @2
    vx
    vy
    relssdv.2
    alrimivv
    wph
    cA
    wrel
    @0
    @3
    wb
    relssdv.1
    vx
    vy
    cA
    cB
    ssrel
    syl
    mpbird
end
