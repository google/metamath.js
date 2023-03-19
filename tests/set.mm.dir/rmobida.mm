include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wrmo.mm"
include "pm5.32da.mm"
include "mobid.mm"
include "df-rmo.mm"
include "3bitr4g.mm"

theorem rmobida
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rmobida.1: |- F/ x ph
  assume rmobida.2: |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) )


  assert |- ( ph -> ( E* x e. A ps <-> E* x e. A ch ) )

  proof
    wph
    vx
    cv
    cA
    wcel
    #
    wps
    wa
    #
    vx
    wmo
    @0
    wch
    wa
    #
    vx
    wmo
    wps
    vx
    cA
    wrmo
    wch
    vx
    cA
    wrmo
    wph
    @1
    @2
    vx
    rmobida.1
    wph
    @0
    wps
    wch
    rmobida.2
    pm5.32da
    mobid
    wps
    vx
    cA
    df-rmo
    wch
    vx
    cA
    df-rmo
    3bitr4g
end
