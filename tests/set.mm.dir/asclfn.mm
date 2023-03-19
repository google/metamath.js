include "cv.mm"
include "cur.mm"
include "cfv.mm"
include "cvsca.mm"
include "co.mm"
include "ovex.mm"
include "eqid.mm"
include "asclfval.mm"
include "fnmpti.mm"

theorem asclfn
  let cA: class A
  let cF: class F
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume asclfn.a: |- A = ( algSc ` W )
  assume asclfn.f: |- F = ( Scalar ` W )
  assume asclfn.k: |- K = ( Base ` F )


  assert |- A Fn K

  proof
    vx
    cK
    vx
    cv
    #
    cW
    cur
    cfv
    #
    cW
    cvsca
    cfv
    #
    co
    cA
    @0
    @1
    @2
    ovex
    vx
    cA
    @2
    @1
    cF
    cK
    cW
    asclfn.a
    asclfn.f
    asclfn.k
    @2
    eqid
    @1
    eqid
    asclfval
    fnmpti
end
