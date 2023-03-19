include "cv.mm"
include "wceq.mm"
include "rmob2.mm"
include "mpbird.mm"

theorem rmoi2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rmoi2.1: |- ( x = B -> ( ps <-> ch ) )
  assume rmoi2.2: |- ( ph -> B e. A )
  assume rmoi2.3: |- ( ph -> E* x e. A ps )
  assume rmoi2.4: |- ( ph -> x e. A )
  assume rmoi2.5: |- ( ph -> ps )
  assume rmoi2.6: |- ( ph -> ch )

  disjoint A x
  disjoint B x
  disjoint ch x
  assert |- ( ph -> x = B )

  proof
    wph
    vx
    cv
    cB
    wceq
    wch
    rmoi2.6
    wph
    wps
    wch
    vx
    cA
    cB
    rmoi2.1
    rmoi2.2
    rmoi2.3
    rmoi2.4
    rmoi2.5
    rmob2
    mpbird
end
