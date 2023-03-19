include "wa.mm"
include "wi.mm"
include "cif.mm"
include "wceq.mm"
include "imbi2d.mm"
include "dedth2h.mm"
include "imp.mm"

theorem dedth4h
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  assume dedth4h.1: |- ( A = if ( ph , A , R ) -> ( ta <-> et ) )
  assume dedth4h.2: |- ( B = if ( ps , B , S ) -> ( et <-> ze ) )
  assume dedth4h.3: |- ( C = if ( ch , C , F ) -> ( ze <-> si ) )
  assume dedth4h.4: |- ( D = if ( th , D , G ) -> ( si <-> rh ) )
  assume dedth4h.5: |- rh


  assert |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta )

  proof
    wph
    wps
    wa
    wch
    wth
    wa
    #
    wta
    wph
    wps
    @0
    wta
    wi
    @0
    wet
    wi
    @0
    wze
    wi
    cA
    cB
    cR
    cS
    cA
    wph
    cA
    cR
    cif
    wceq
    wta
    wet
    @0
    dedth4h.1
    imbi2d
    cB
    wps
    cB
    cS
    cif
    wceq
    wet
    wze
    @0
    dedth4h.2
    imbi2d
    wch
    wth
    wze
    wsi
    wrh
    cC
    cD
    cF
    cG
    dedth4h.3
    dedth4h.4
    dedth4h.5
    dedth2h
    dedth2h
    imp
end
