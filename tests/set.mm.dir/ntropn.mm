include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cnt.mm"
include "cfv.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "ntrval.mm"
include "inss1.mm"
include "uniopn.mm"
include "mpan2.mm"
include "adantr.mm"
include "eqeltrd.mm"

theorem ntropn
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


  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( int ` J ) ` S ) e. J )

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
    cS
    cJ
    cnt
    cfv
    cfv
    cJ
    cS
    cpw
    #
    cin
    #
    cuni
    #
    cJ
    cS
    cJ
    cX
    clscld.1
    ntrval
    @0
    @4
    cJ
    wcel
    #
    @1
    @0
    @3
    cJ
    wss
    @5
    cJ
    @2
    inss1
    @3
    cJ
    uniopn
    mpan2
    adantr
    eqeltrd
end
