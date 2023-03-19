include "wfis2.mm"
include "vtoclga.mm"

theorem wfis3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  assume wfis3.1: |- R We A
  assume wfis3.2: |- R Se A
  assume wfis3.3: |- ( y = z -> ( ph <-> ps ) )
  assume wfis3.4: |- ( y = B -> ( ph <-> ch ) )
  assume wfis3.5: |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint B y
  disjoint ch y
  disjoint ph z
  disjoint ps y
  disjoint R y
  disjoint R z
  assert |- ( B e. A -> ch )

  proof
    wph
    wch
    vy
    cB
    cA
    wfis3.4
    wph
    wps
    vy
    vz
    cA
    cR
    wfis3.1
    wfis3.2
    wfis3.3
    wfis3.5
    wfis2
    vtoclga
end
