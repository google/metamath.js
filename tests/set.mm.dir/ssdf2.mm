include "cv.mm"
include "wcel.mm"
include "ex.mm"
include "ssrd.mm"

theorem ssdf2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ssdf2.p: |- F/ x ph
  assume ssdf2.a: |- F/_ x A
  assume ssdf2.b: |- F/_ x B
  assume ssdf2.x: |- ( ( ph /\ x e. A ) -> x e. B )


  assert |- ( ph -> A C_ B )

  proof
    wph
    vx
    cA
    cB
    ssdf2.p
    ssdf2.a
    ssdf2.b
    wph
    vx
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
    ssdf2.x
    ex
    ssrd
end
