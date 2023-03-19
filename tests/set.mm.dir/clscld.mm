include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "cv.mm"
include "ccld.mm"
include "crab.mm"
include "cint.mm"
include "clsval.mm"
include "c0.mm"
include "wne.mm"
include "topcld.mm"
include "anim1i.mm"
include "sseq2.mm"
include "elrab.mm"
include "sylibr.mm"
include "ne0i.mm"
include "syl.mm"
include "ssrab2.mm"
include "intcld.mm"
include "sylancl.mm"
include "eqeltrd.mm"

theorem clscld
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cU: class U
  let cT: class T
  let cA: class A
  assume clscld.1: |- X = U. J


  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( cls ` J ) ` S ) e. ( Clsd ` J ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cS
    cJ
    ccl
    cfv
    cfv
    cS
    vx
    cv
    #
    wss
    #
    vx
    cJ
    ccld
    cfv
    #
    crab
    #
    cint
    #
    @5
    vx
    cS
    cJ
    cX
    clscld.1
    clsval
    @2
    @6
    c0
    wne
    #
    @6
    @5
    wss
    @7
    @5
    wcel
    @2
    cX
    @6
    wcel
    #
    @8
    @2
    cX
    @5
    wcel
    #
    @1
    wa
    @9
    @0
    @10
    @1
    cJ
    cX
    clscld.1
    topcld
    anim1i
    @4
    @1
    vx
    cX
    @5
    @3
    cX
    cS
    sseq2
    elrab
    sylibr
    @6
    cX
    ne0i
    syl
    @4
    vx
    @5
    ssrab2
    @6
    cJ
    intcld
    sylancl
    eqeltrd
end
