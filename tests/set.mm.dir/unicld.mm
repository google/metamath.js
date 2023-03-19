include "ctop.mm"
include "wcel.mm"
include "cfn.mm"
include "ccld.mm"
include "cfv.mm"
include "wss.mm"
include "w3a.mm"
include "cuni.mm"
include "cv.mm"
include "ciun.mm"
include "uniiun.mm"
include "wral.mm"
include "dfss3.mm"
include "iuncld.mm"
include "syl3an3b.mm"
include "syl5eqel.mm"

theorem unicld
  let cA: class A
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cS: class S
  let cU: class U
  let cT: class T
  assume clscld.1: |- X = U. J


  assert |- ( ( J e. Top /\ A e. Fin /\ A C_ ( Clsd ` J ) ) -> U. A e. ( Clsd ` J ) )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cfn
    wcel
    #
    cA
    cJ
    ccld
    cfv
    #
    wss
    #
    w3a
    cA
    cuni
    vx
    cA
    vx
    cv
    #
    ciun
    #
    @2
    vx
    cA
    uniiun
    @3
    @0
    @1
    @4
    @2
    wcel
    vx
    cA
    wral
    @5
    @2
    wcel
    vx
    cA
    @2
    dfss3
    vx
    cA
    @4
    cJ
    cX
    clscld.1
    iuncld
    syl3an3b
    syl5eqel
end
