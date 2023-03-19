include "wi.mm"
include "cif.mm"
include "wceq.mm"
include "imbi2d.mm"
include "dedth.mm"
include "imp.mm"

theorem dedth2h
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume dedth2h.1: |- ( A = if ( ph , A , C ) -> ( ch <-> th ) )
  assume dedth2h.2: |- ( B = if ( ps , B , D ) -> ( th <-> ta ) )
  assume dedth2h.3: |- ta


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wch
    wph
    wps
    wch
    wi
    wps
    wth
    wi
    cA
    cC
    cA
    wph
    cA
    cC
    cif
    wceq
    wch
    wth
    wps
    dedth2h.1
    imbi2d
    wps
    wth
    wta
    cB
    cD
    dedth2h.2
    dedth2h.3
    dedth
    dedth
    imp
end
