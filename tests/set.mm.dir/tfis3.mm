include "con0.mm"
include "tfis2.mm"
include "vtoclga.mm"

theorem tfis3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume tfis3.1: |- ( x = y -> ( ph <-> ps ) )
  assume tfis3.2: |- ( x = A -> ( ph <-> ch ) )
  assume tfis3.3: |- ( x e. On -> ( A. y e. x ps -> ph ) )

  disjoint ps x
  disjoint ph y
  disjoint ch x
  disjoint A x
  disjoint x y
  assert |- ( A e. On -> ch )

  proof
    wph
    wch
    vx
    cA
    con0
    tfis3.2
    wph
    wps
    vx
    vy
    tfis3.1
    tfis3.3
    tfis2
    vtoclga
end
