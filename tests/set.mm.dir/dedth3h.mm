include "wa.mm"
include "wi.mm"
include "cif.mm"
include "wceq.mm"
include "imbi2d.mm"
include "dedth2h.mm"
include "dedth.mm"
include "3impib.mm"

theorem dedth3h
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  assume dedth3h.1: |- ( A = if ( ph , A , D ) -> ( th <-> ta ) )
  assume dedth3h.2: |- ( B = if ( ps , B , R ) -> ( ta <-> et ) )
  assume dedth3h.3: |- ( C = if ( ch , C , S ) -> ( et <-> ze ) )
  assume dedth3h.4: |- ze


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wa
    #
    wth
    wi
    @0
    wta
    wi
    cA
    cD
    cA
    wph
    cA
    cD
    cif
    wceq
    wth
    wta
    @0
    dedth3h.1
    imbi2d
    wps
    wch
    wta
    wet
    wze
    cB
    cC
    cR
    cS
    dedth3h.2
    dedth3h.3
    dedth3h.4
    dedth2h
    dedth
    3impib
end
