include "weu.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wreu.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "eubidv.mm"
include "df-reu.mm"
include "syl6rbbr.mm"

theorem reueubd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cV: class V
  assume reueubd.1: |- ( ( ph /\ ps ) -> x e. V )

  disjoint ph x
  assert |- ( ph -> ( E! x e. V ps <-> E! x ps ) )

  proof
    wph
    wps
    vx
    weu
    vx
    cv
    cV
    wcel
    #
    wps
    wa
    #
    vx
    weu
    wps
    vx
    cV
    wreu
    wph
    wps
    @1
    vx
    wph
    wps
    @0
    wph
    wps
    @0
    reueubd.1
    ex
    pm4.71rd
    eubidv
    wps
    vx
    cV
    df-reu
    syl6rbbr
end
