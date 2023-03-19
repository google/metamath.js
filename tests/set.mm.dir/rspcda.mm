include "wcel.mm"
include "wral.mm"
include "rspcv.mm"
include "sylc.mm"

theorem rspcda
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cC: class C
  assume rspcdva.1: |- ( x = C -> ( ps <-> ch ) )
  assume rspcdva.2: |- ( ph -> A. x e. A ps )
  assume rspcdva.3: |- ( ph -> C e. A )
  assume rspcda.1: |- F/ x ph

  disjoint A x
  disjoint C x
  disjoint ch x
  assert |- ( ph -> ch )

  proof
    wph
    cC
    cA
    wcel
    wps
    vx
    cA
    wral
    wch
    rspcdva.3
    rspcdva.2
    wps
    wch
    vx
    cC
    cA
    rspcdva.1
    rspcv
    sylc
end
