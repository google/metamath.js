include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wss.mm"
include "alrimiv.mm"
include "dfss2.mm"
include "sylibr.mm"

theorem ssrdv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ssrdv.1: |- ( ph -> ( x e. A -> x e. B ) )

  disjoint A x
  disjoint B x
  disjoint ph x
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
    #
    vx
    wal
    cA
    cB
    wss
    wph
    @1
    vx
    ssrdv.1
    alrimiv
    vx
    cA
    cB
    dfss2
    sylibr
end
