include "cv.mm"
include "cclwwlk.mm"
include "cfv.mm"
include "wcel.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "wrex.mm"
include "w3a.mm"
include "relopabi.mm"

theorem erclwwlkrel
  let vw: setvar w
  let vu: setvar u
  let c.sm: class .~
  let vn: setvar n
  let cG: class G
  assume erclwwlk.r: |- .~ = { <. u , w >. | ( u e. ( ClWWalks ` G ) /\ w e. ( ClWWalks ` G ) /\ E. n e. ( 0 ... ( # ` w ) ) u = ( w cyclShift n ) ) }


  assert |- Rel .~

  proof
    vu
    cv
    #
    cG
    cclwwlk
    cfv
    #
    wcel
    vw
    cv
    #
    @1
    wcel
    @0
    @2
    vn
    cv
    ccsh
    co
    wceq
    vn
    cc0
    @2
    chash
    cfv
    cfz
    co
    wrex
    w3a
    vu
    vw
    c.sm
    erclwwlk.r
    relopabi
end
