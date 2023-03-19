include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wss.mm"
include "alrimi.mm"
include "dfss2f.mm"
include "sylibr.mm"

theorem ssrd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ssrd.0: |- F/ x ph
  assume ssrd.1: |- F/_ x A
  assume ssrd.2: |- F/_ x B
  assume ssrd.3: |- ( ph -> ( x e. A -> x e. B ) )


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
    ssrd.0
    ssrd.3
    alrimi
    vx
    cA
    cB
    ssrd.1
    ssrd.2
    dfss2f
    sylibr
end
