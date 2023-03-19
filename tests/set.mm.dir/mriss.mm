include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cmrc.mm"
include "wn.mm"
include "wral.mm"
include "eqid.mm"
include "ismri.mm"
include "simprbda.mm"

theorem mriss
  let cA: class A
  let cS: class S
  let cI: class I
  let cX: class X
  let vx: setvar x
  assume mriss.1: |- I = ( mrInd ` A )


  assert |- ( ( A e. ( Moore ` X ) /\ S e. I ) -> S C_ X )

  proof
    cA
    cX
    cmre
    cfv
    wcel
    cS
    cI
    wcel
    cS
    cX
    wss
    vx
    cv
    #
    cS
    @0
    csn
    cdif
    cA
    cmrc
    cfv
    #
    cfv
    wcel
    wn
    vx
    cS
    wral
    vx
    cA
    cS
    cI
    @1
    cX
    @1
    eqid
    mriss.1
    ismri
    simprbda
end
