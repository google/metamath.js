include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wss.mm"
include "dfss2.mm"
include "sylibr.mm"

theorem bnj1361
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume bnj1361.1: |- ( ph -> A. x ( x e. A -> x e. B ) )

  disjoint A x
  disjoint B x
  assert |- ( ph -> A C_ B )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
    wi
    vx
    wal
    cA
    cB
    wss
    bnj1361.1
    vx
    cA
    cB
    dfss2
    sylibr
end
