include "cvoln.mm"
include "cfv.mm"
include "covoln.mm"
include "ccaragen.mm"
include "cres.mm"
include "cmea.mm"
include "vonval.mm"
include "ovnome.mm"
include "eqid.mm"
include "caratheodory.mm"
include "eqeltrd.mm"

theorem vonmea
  let wph: wff ph
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume vonmea.1: |- ( ph -> X e. Fin )


  assert |- ( ph -> ( voln ` X ) e. Meas )

  proof
    wph
    cX
    cvoln
    cfv
    cX
    covoln
    cfv
    #
    @0
    ccaragen
    cfv
    #
    cres
    cmea
    wph
    cX
    vonmea.1
    vonval
    wph
    @1
    @0
    wph
    cX
    vonmea.1
    ovnome
    @1
    eqid
    caratheodory
    eqeltrd
end
