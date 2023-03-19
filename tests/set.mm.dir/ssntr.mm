include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "cnt.mm"
include "cfv.mm"
include "elin.mm"
include "elpwg.mm"
include "pm5.32i.mm"
include "bitr2i.mm"
include "elssuni.mm"
include "sylbi.mm"
include "adantl.mm"
include "wceq.mm"
include "ntrval.mm"
include "adantr.mm"
include "sseqtr4d.mm"

theorem ssntr
  let cS: class S
  let cJ: class J
  let cO: class O
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cU: class U
  let cT: class T
  let cA: class A
  assume clscld.1: |- X = U. J


  assert |- ( ( ( J e. Top /\ S C_ X ) /\ ( O e. J /\ O C_ S ) ) -> O C_ ( ( int ` J ) ` S ) )

  proof
    cJ
    ctop
    wcel
    cS
    cX
    wss
    wa
    #
    cO
    cJ
    wcel
    #
    cO
    cS
    wss
    #
    wa
    #
    wa
    cO
    cJ
    cS
    cpw
    #
    cin
    #
    cuni
    #
    cS
    cJ
    cnt
    cfv
    cfv
    #
    @3
    cO
    @6
    wss
    #
    @0
    @3
    cO
    @5
    wcel
    #
    @8
    @9
    @1
    cO
    @4
    wcel
    #
    wa
    @3
    cO
    cJ
    @4
    elin
    @1
    @10
    @2
    cO
    cS
    cJ
    elpwg
    pm5.32i
    bitr2i
    cO
    @5
    elssuni
    sylbi
    adantl
    @0
    @7
    @6
    wceq
    @3
    cS
    cJ
    cX
    clscld.1
    ntrval
    adantr
    sseqtr4d
end
