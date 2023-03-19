include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccld.mm"
include "cfv.mm"
include "ccl.mm"
include "wceq.mm"
include "iscld3.mm"
include "sscls.mm"
include "biantrud.mm"
include "eqss.mm"
include "syl6rbbr.mm"
include "bitrd.mm"

theorem iscld4
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


  assert |- ( ( J e. Top /\ S C_ X ) -> ( S e. ( Clsd ` J ) <-> ( ( cls ` J ) ` S ) C_ S ) )

  proof
    cJ
    ctop
    wcel
    cS
    cX
    wss
    wa
    #
    cS
    cJ
    ccld
    cfv
    wcel
    cS
    cJ
    ccl
    cfv
    cfv
    #
    cS
    wceq
    #
    @1
    cS
    wss
    #
    cS
    cJ
    cX
    clscld.1
    iscld3
    @0
    @3
    @3
    cS
    @1
    wss
    #
    wa
    @2
    @0
    @4
    @3
    cS
    cJ
    cX
    clscld.1
    sscls
    biantrud
    @1
    cS
    eqss
    syl6rbbr
    bitrd
end
