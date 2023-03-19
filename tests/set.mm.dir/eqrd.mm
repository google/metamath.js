include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wceq.mm"
include "alrimi.mm"
include "cleqf.mm"
include "sylibr.mm"

theorem eqrd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume eqrd.0: |- F/ x ph
  assume eqrd.1: |- F/_ x A
  assume eqrd.2: |- F/_ x B
  assume eqrd.3: |- ( ph -> ( x e. A <-> x e. B ) )


  assert |- ( ph -> A = B )

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
    wb
    #
    vx
    wal
    cA
    cB
    wceq
    wph
    @1
    vx
    eqrd.0
    eqrd.3
    alrimi
    vx
    cA
    cB
    eqrd.1
    eqrd.2
    cleqf
    sylibr
end
