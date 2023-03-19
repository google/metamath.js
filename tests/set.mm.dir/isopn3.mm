include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cnt.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "ntrval.mm"
include "inss2.mm"
include "unissi.mm"
include "unipw.mm"
include "sseqtri.mm"
include "a1i.mm"
include "id.mm"
include "pwidg.mm"
include "elind.mm"
include "elssuni.mm"
include "syl.mm"
include "eqssd.mm"
include "sylan9eq.mm"
include "ex.mm"
include "ntropn.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "impbid.mm"

theorem isopn3
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


  assert |- ( ( J e. Top /\ S C_ X ) -> ( S e. J <-> ( ( int ` J ) ` S ) = S ) )

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
    wcel
    #
    cS
    cJ
    cnt
    cfv
    cfv
    #
    cS
    wceq
    #
    @0
    @1
    @3
    @0
    @1
    @2
    cJ
    cS
    cpw
    #
    cin
    #
    cuni
    #
    cS
    cS
    cJ
    cX
    clscld.1
    ntrval
    @1
    @6
    cS
    @6
    cS
    wss
    @1
    @6
    @4
    cuni
    cS
    @5
    @4
    cJ
    @4
    inss2
    unissi
    cS
    unipw
    sseqtri
    a1i
    @1
    cS
    @5
    wcel
    cS
    @6
    wss
    @1
    cJ
    @4
    cS
    @1
    id
    cS
    cJ
    pwidg
    elind
    cS
    @5
    elssuni
    syl
    eqssd
    sylan9eq
    ex
    @0
    @2
    cJ
    wcel
    @3
    @1
    cS
    cJ
    cX
    clscld.1
    ntropn
    @2
    cS
    cJ
    eleq1
    syl5ibcom
    impbid
end
