include "crg.mm"
include "wcel.mm"
include "zring.mm"
include "crh.mm"
include "co.mm"
include "csn.mm"
include "wceq.mm"
include "cz.mm"
include "cv.mm"
include "cur.mm"
include "cfv.mm"
include "cmg.mm"
include "cmpt.mm"
include "eqid.mm"
include "mulgrhm2.mm"
include "zrhval2.mm"
include "sneqd.mm"
include "eqtr4d.mm"
include "eleq2d.mm"
include "czrh.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elsn2.mm"
include "syl6bb.mm"

theorem zrhrhmb
  let cR: class R
  let cF: class F
  let cL: class L
  let vr: setvar r
  let vs: setvar s
  let cN: class N
  let vn: setvar n
  let c.1: class .1.
  let c.x: class .x.
  assume zrhval.l: |- L = ( ZRHom ` R )


  assert |- ( R e. Ring -> ( F e. ( ZZring RingHom R ) <-> F = L ) )

  proof
    cR
    crg
    wcel
    #
    cF
    zring
    cR
    crh
    co
    #
    wcel
    cF
    cL
    csn
    #
    wcel
    cF
    cL
    wceq
    @0
    @1
    @2
    cF
    @0
    @1
    vn
    cz
    vn
    cv
    cR
    cur
    cfv
    #
    cR
    cmg
    cfv
    #
    co
    cmpt
    #
    csn
    @2
    cR
    @4
    @3
    vn
    @5
    @4
    eqid
    #
    @5
    eqid
    @3
    eqid
    #
    mulgrhm2
    @0
    cL
    @5
    cR
    @4
    @3
    vn
    cL
    zrhval.l
    @6
    @7
    zrhval2
    sneqd
    eqtr4d
    eleq2d
    cF
    cL
    cL
    cR
    czrh
    cfv
    cvv
    zrhval.l
    cR
    czrh
    fvex
    eqeltri
    elsn2
    syl6bb
end
