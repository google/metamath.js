include "dedth3h.mm"
include "3anidm12.mm"
include "anidms.mm"

theorem dedth3v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  assume dedth3v.1: |- ( A = if ( ph , A , D ) -> ( ps <-> ch ) )
  assume dedth3v.2: |- ( B = if ( ph , B , R ) -> ( ch <-> th ) )
  assume dedth3v.3: |- ( C = if ( ph , C , S ) -> ( th <-> ta ) )
  assume dedth3v.4: |- ta


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wph
    wph
    wps
    wph
    wph
    wph
    wps
    wch
    wth
    wta
    cA
    cB
    cC
    cD
    cR
    cS
    dedth3v.1
    dedth3v.2
    dedth3v.3
    dedth3v.4
    dedth3h
    3anidm12
    anidms
end
