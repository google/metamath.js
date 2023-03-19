include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cmpt2.mm"
include "eqid.mm"
include "xpstopnlem2.mm"

theorem xpstopn
  let cR: class R
  let cS: class S
  let cT: class T
  let cJ: class J
  let cK: class K
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cY: class Y
  assume xpstps.t: |- T = ( R Xs. S )
  assume xpstopn.j: |- J = ( TopOpen ` R )
  assume xpstopn.k: |- K = ( TopOpen ` S )
  assume xpstopn.o: |- O = ( TopOpen ` T )


  assert |- ( ( R e. TopSp /\ S e. TopSp ) -> O = ( J tX K ) )

  proof
    vx
    vy
    cR
    cS
    cT
    vx
    vy
    cR
    cbs
    cfv
    #
    cS
    cbs
    cfv
    #
    vx
    cv
    csn
    vy
    cv
    csn
    ccda
    co
    ccnv
    cmpt2
    #
    cJ
    cK
    cO
    @0
    @1
    xpstps.t
    xpstopn.j
    xpstopn.k
    xpstopn.o
    @0
    eqid
    @1
    eqid
    @2
    eqid
    xpstopnlem2
end
