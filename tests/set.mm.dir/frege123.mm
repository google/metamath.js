include "ccnv.mm"
include "wfun.mm"
include "wbr.mm"
include "cv.mm"
include "ctcl.mm"
include "cfv.mm"
include "cid.mm"
include "cun.mm"
include "wi.mm"
include "wal.mm"
include "cvv.mm"
include "vex.mm"
include "frege122.mm"
include "alrimdv.mm"
include "frege19.mm"
include "ax-mp.mm"

theorem frege123
  let cR: class R
  let cU: class U
  let cM: class M
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume frege123.x: |- X e. U
  assume frege123.y: |- Y e. V

  disjoint R a
  disjoint X a
  disjoint Y a
  assert |- ( ( A. a ( Y R a -> X ( ( t+ ` R ) u. _I ) a ) -> ( Y ( t+ ` R ) M -> X ( ( t+ ` R ) u. _I ) M ) ) -> ( Fun `' `' R -> ( Y R X -> ( Y ( t+ ` R ) M -> X ( ( t+ ` R ) u. _I ) M ) ) ) )

  proof
    cR
    ccnv
    ccnv
    wfun
    #
    cY
    cX
    cR
    wbr
    #
    cY
    va
    cv
    #
    cR
    wbr
    cX
    @2
    cR
    ctcl
    cfv
    #
    cid
    cun
    #
    wbr
    wi
    #
    va
    wal
    #
    wi
    wi
    @6
    cY
    cM
    @3
    wbr
    cX
    cM
    @4
    wbr
    wi
    #
    wi
    @0
    @1
    @7
    wi
    wi
    wi
    @0
    @1
    @5
    va
    @2
    cR
    cU
    cV
    cvv
    cX
    cY
    frege123.x
    frege123.y
    va
    vex
    frege122
    alrimdv
    @0
    @1
    @6
    @7
    frege19
    ax-mp
end
