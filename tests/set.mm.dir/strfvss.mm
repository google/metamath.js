include "cvv.mm"
include "wcel.mm"
include "cfv.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "id.mm"
include "strfvnd.mm"
include "fvssunirn.mm"
include "syl6eqss.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "0ss.mm"
include "pm2.61i.mm"

theorem strfvss
  let cS: class S
  let cE: class E
  let cN: class N
  assume ndxarg.1: |- E = Slot N


  assert |- ( E ` S ) C_ U. ran S

  proof
    cS
    cvv
    wcel
    #
    cS
    cE
    cfv
    #
    cS
    crn
    cuni
    #
    wss
    @0
    @1
    cN
    cS
    cfv
    @2
    @0
    cS
    cE
    cN
    cvv
    ndxarg.1
    @0
    id
    strfvnd
    cS
    cN
    fvssunirn
    syl6eqss
    @0
    wn
    @1
    c0
    @2
    cS
    cE
    fvprc
    @2
    0ss
    syl6eqss
    pm2.61i
end
