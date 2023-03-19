include "cc0.mm"
include "cpi.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "ccos.mm"
include "cfv.mm"
include "cneg.mm"
include "cmpt.mm"
include "eqid.mm"
include "itgsin0pilem1.mm"

theorem itgsin0pi
  let vx: setvar x
  let vt: setvar t
  let vk: setvar k


  assert |- S. ( 0 (,) _pi ) ( sin ` x ) _d x = 2

  proof
    vx
    vt
    vt
    cc0
    cpi
    cicc
    co
    vt
    cv
    ccos
    cfv
    cneg
    cmpt
    #
    @0
    eqid
    itgsin0pilem1
end
