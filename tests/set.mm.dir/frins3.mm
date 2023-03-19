include "frins2.mm"
include "vtoclga.mm"

theorem frins3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  assume frins3.1: |- R Fr A
  assume frins3.2: |- R Se A
  assume frins3.3: |- ( y = z -> ( ph <-> ps ) )
  assume frins3.4: |- ( y = B -> ( ph <-> ch ) )
  assume frins3.5: |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint B y
  disjoint ph z
  disjoint ps y
  disjoint ch y
  disjoint R y
  disjoint R z
  assert |- ( B e. A -> ch )

  proof
    wph
    wch
    vy
    cB
    cA
    frins3.4
    wph
    wps
    vy
    vz
    cA
    cR
    frins3.1
    frins3.2
    frins3.3
    frins3.5
    frins2
    vtoclga
end
