include "cop.mm"
include "cnv.mm"
include "wcel.mm"
include "cvc.mm"
include "cvv.mm"
include "cxp.mm"
include "nvss.mm"
include "sseli.mm"
include "opelxp1.mm"
include "syl.mm"

theorem nvvcop
  let cN: class N
  let cW: class W
  let vg: setvar g
  let vs: setvar s
  let vn: setvar n
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y


  assert |- ( <. W , N >. e. NrmCVec -> W e. CVecOLD )

  proof
    cW
    cN
    cop
    #
    cnv
    wcel
    @0
    cvc
    cvv
    cxp
    #
    wcel
    cW
    cvc
    wcel
    cnv
    @1
    @0
    nvss
    sseli
    cW
    cN
    cvc
    cvv
    opelxp1
    syl
end
