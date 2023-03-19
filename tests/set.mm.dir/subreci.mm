include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "cmul.mm"
include "wceq.mm"
include "subrec.mm"
include "mp4an.mm"

theorem subreci
  let cA: class A
  let cB: class B
  assume subreci.1: |- A e. CC
  assume subreci.2: |- B e. CC
  assume subreci.3: |- A =/= 0
  assume subreci.4: |- B =/= 0


  assert |- ( ( 1 / A ) - ( 1 / B ) ) = ( ( B - A ) / ( A x. B ) )

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    cB
    cc
    wcel
    cB
    cc0
    wne
    c1
    cA
    cdiv
    co
    c1
    cB
    cdiv
    co
    cmin
    co
    cB
    cA
    cmin
    co
    cA
    cB
    cmul
    co
    cdiv
    co
    wceq
    subreci.1
    subreci.3
    subreci.2
    subreci.4
    cA
    cB
    subrec
    mp4an
end
