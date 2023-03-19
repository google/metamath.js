include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weu.mm"
include "wreu.mm"
include "pm5.32da.mm"
include "eubid.mm"
include "df-reu.mm"
include "3bitr4g.mm"

theorem reubida
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume reubida.1: |- F/ x ph
  assume reubida.2: |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) )


  assert |- ( ph -> ( E! x e. A ps <-> E! x e. A ch ) )

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
    weu
    @0
    wch
    wa
    #
    vx
    weu
    wps
    vx
    cA
    wreu
    wch
    vx
    cA
    wreu
    wph
    @1
    @2
    vx
    reubida.1
    wph
    @0
    wps
    wch
    reubida.2
    pm5.32da
    eubid
    wps
    vx
    cA
    df-reu
    wch
    vx
    cA
    df-reu
    3bitr4g
end
