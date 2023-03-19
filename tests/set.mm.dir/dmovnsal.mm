include "cvoln.mm"
include "cfv.mm"
include "vonmea.mm"
include "dmmeasal.mm"

theorem dmovnsal
  let wph: wff ph
  let cS: class S
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume dmovnsal.x: |- ( ph -> X e. Fin )
  assume dmovnsal.s: |- S = dom ( voln ` X )


  assert |- ( ph -> S e. SAlg )

  proof
    wph
    cS
    cX
    cvoln
    cfv
    wph
    cX
    dmovnsal.x
    vonmea
    dmovnsal.s
    dmmeasal
end
