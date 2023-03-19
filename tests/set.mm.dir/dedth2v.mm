include "dedth2h.mm"
include "anidms.mm"

theorem dedth2v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume dedth2v.1: |- ( A = if ( ph , A , C ) -> ( ps <-> ch ) )
  assume dedth2v.2: |- ( B = if ( ph , B , D ) -> ( ch <-> th ) )
  assume dedth2v.3: |- th


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wph
    wph
    wps
    wch
    wth
    cA
    cB
    cC
    cD
    dedth2v.1
    dedth2v.2
    dedth2v.3
    dedth2h
    anidms
end
