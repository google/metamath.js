include "wcel.mm"
include "cpw.mm"
include "ccmp.mm"
include "clly.mm"
include "cv.mm"
include "csn.mm"
include "wral.mm"
include "cfn.mm"
include "snfi.mm"
include "discmp.mm"
include "mpbi.mm"
include "rgenw.mm"
include "dislly.mm"
include "mpbiri.mm"

theorem disllycmp
  let cV: class V
  let cX: class X
  let va: setvar a
  let vj: setvar j
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vs: setvar s
  let cA: class A
  let cJ: class J


  assert |- ( X e. V -> ~P X e. Locally Comp )

  proof
    cX
    cV
    wcel
    cX
    cpw
    ccmp
    clly
    wcel
    vx
    cv
    #
    csn
    #
    cpw
    ccmp
    wcel
    #
    vx
    cX
    wral
    @2
    vx
    cX
    @1
    cfn
    wcel
    @2
    @0
    snfi
    @1
    discmp
    mpbi
    rgenw
    vx
    ccmp
    cV
    cX
    dislly
    mpbiri
end
