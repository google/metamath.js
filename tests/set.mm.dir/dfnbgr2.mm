include "wcel.mm"
include "cnbgr.mm"
include "co.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wa.mm"
include "nbgrval.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "prssg.mm"
include "mpan2.mm"
include "bicomd.mm"
include "rexbidv.mm"
include "rabbidv.mm"
include "eqtrd.mm"

theorem dfnbgr2
  let ve: setvar e
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let vg: setvar g
  let vk: setvar k
  assume nbgrval.v: |- V = ( Vtx ` G )
  assume nbgrval.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint G e
  disjoint G n
  disjoint e n
  disjoint N e
  disjoint N n
  disjoint V e
  disjoint V n
  disjoint E g
  disjoint E k
  disjoint e g
  disjoint e k
  disjoint g k
  disjoint G g
  disjoint G k
  disjoint g n
  disjoint k n
  disjoint N g
  disjoint N k
  disjoint V g
  disjoint V k
  assert |- ( N e. V -> ( G NeighbVtx N ) = { n e. ( V \ { N } ) | E. e e. E ( N e. e /\ n e. e ) } )

  proof
    cN
    cV
    wcel
    #
    cG
    cN
    cnbgr
    co
    cN
    vn
    cv
    #
    cpr
    ve
    cv
    #
    wss
    #
    ve
    cE
    wrex
    #
    vn
    cV
    cN
    csn
    cdif
    #
    crab
    cN
    @2
    wcel
    @1
    @2
    wcel
    wa
    #
    ve
    cE
    wrex
    #
    vn
    @5
    crab
    ve
    vn
    cE
    cG
    cN
    cV
    nbgrval.v
    nbgrval.e
    nbgrval
    @0
    @4
    @7
    vn
    @5
    @0
    @3
    @6
    ve
    cE
    @0
    @6
    @3
    @0
    @1
    cvv
    wcel
    @6
    @3
    wb
    vn
    vex
    cN
    @1
    @2
    cV
    cvv
    prssg
    mpan2
    bicomd
    rexbidv
    rabbidv
    eqtrd
end
