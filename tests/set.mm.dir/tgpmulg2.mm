include "ctgp.mm"
include "wcel.mm"
include "cvv.mm"
include "cz.mm"
include "cbs.mm"
include "cfv.mm"
include "zex.mm"
include "a1i.mm"
include "eqid.mm"
include "tgptopon.mm"
include "ctopon.mm"
include "ctop.mm"
include "topontop.mm"
include "syl.mm"
include "cxp.mm"
include "wfn.mm"
include "mulgfn.mm"
include "cv.mm"
include "tgpmulg.mm"
include "txdis1cn.mm"

theorem tgpmulg2
  let c.x: class .x.
  let cG: class G
  let cJ: class J
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cN: class N
  assume tgpmulg.j: |- J = ( TopOpen ` G )
  assume tgpmulg.t: |- .x. = ( .g ` G )


  assert |- ( G e. TopGrp -> .x. e. ( ( ~P ZZ tX J ) Cn J ) )

  proof
    cG
    ctgp
    wcel
    #
    vn
    vx
    c.x
    cJ
    cJ
    cvv
    cz
    cG
    cbs
    cfv
    #
    cz
    cvv
    wcel
    @0
    zex
    a1i
    cG
    cJ
    @1
    tgpmulg.j
    @1
    eqid
    #
    tgptopon
    #
    @0
    cJ
    @1
    ctopon
    cfv
    wcel
    cJ
    ctop
    wcel
    @3
    @1
    cJ
    topontop
    syl
    c.x
    cz
    @1
    cxp
    wfn
    @0
    @1
    c.x
    cG
    @2
    tgpmulg.t
    mulgfn
    a1i
    vx
    @1
    c.x
    cG
    cJ
    vn
    cv
    tgpmulg.j
    tgpmulg.t
    @2
    tgpmulg
    txdis1cn
end
