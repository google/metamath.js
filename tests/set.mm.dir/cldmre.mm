include "ctop.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "cpw.mm"
include "wss.mm"
include "cldss2.mm"
include "a1i.mm"
include "topcld.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cint.mm"
include "intcld.mm"
include "ancoms.mm"
include "3adant1.mm"
include "ismred.mm"

theorem cldmre
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cS: class S
  let cU: class U
  let cT: class T
  let cA: class A
  assume clscld.1: |- X = U. J


  assert |- ( J e. Top -> ( Clsd ` J ) e. ( Moore ` X ) )

  proof
    cJ
    ctop
    wcel
    #
    cJ
    ccld
    cfv
    #
    cX
    vx
    @1
    cX
    cpw
    wss
    @0
    cJ
    cX
    clscld.1
    cldss2
    a1i
    cJ
    cX
    clscld.1
    topcld
    vx
    cv
    #
    @1
    wss
    #
    @2
    c0
    wne
    #
    @2
    cint
    @1
    wcel
    #
    @0
    @4
    @3
    @5
    @2
    cJ
    intcld
    ancoms
    3adant1
    ismred
end
