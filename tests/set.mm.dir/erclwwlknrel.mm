include "cv.mm"
include "wcel.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "w3a.mm"
include "relopabi.mm"

theorem erclwwlknrel
  let vu: setvar u
  let vt: setvar t
  let c.sm: class .~
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cW: class W
  assume erclwwlkn.w: |- W = ( N ClWWalksN G )
  assume erclwwlkn.r: |- .~ = { <. t , u >. | ( t e. W /\ u e. W /\ E. n e. ( 0 ... N ) t = ( u cyclShift n ) ) }


  assert |- Rel .~

  proof
    vt
    cv
    #
    cW
    wcel
    vu
    cv
    #
    cW
    wcel
    @0
    @1
    vn
    cv
    ccsh
    co
    wceq
    vn
    cc0
    cN
    cfz
    co
    wrex
    w3a
    vt
    vu
    c.sm
    erclwwlkn.r
    relopabi
end
