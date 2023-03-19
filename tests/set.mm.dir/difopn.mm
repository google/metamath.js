include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "wa.mm"
include "cin.mm"
include "cdif.mm"
include "wss.mm"
include "wceq.mm"
include "cuni.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "adantr.mm"
include "df-ss.mm"
include "sylib.mm"
include "difeq1d.mm"
include "indif2.mm"
include "ctop.mm"
include "cldrcl.mm"
include "adantl.mm"
include "simpl.mm"
include "cldopn.mm"
include "inopn.mm"
include "syl3anc.mm"
include "syl5eqelr.mm"
include "eqeltrrd.mm"

theorem difopn
  let cA: class A
  let cB: class B
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  assume iscld.1: |- X = U. J


  assert |- ( ( A e. J /\ B e. ( Clsd ` J ) ) -> ( A \ B ) e. J )

  proof
    cA
    cJ
    wcel
    #
    cB
    cJ
    ccld
    cfv
    wcel
    #
    wa
    #
    cA
    cX
    cin
    #
    cB
    cdif
    #
    cA
    cB
    cdif
    cJ
    @2
    @3
    cA
    cB
    @2
    cA
    cX
    wss
    #
    @3
    cA
    wceq
    @0
    @5
    @1
    @0
    cA
    cJ
    cuni
    cX
    cA
    cJ
    elssuni
    iscld.1
    syl6sseqr
    adantr
    cA
    cX
    df-ss
    sylib
    difeq1d
    @2
    @4
    cA
    cX
    cB
    cdif
    #
    cin
    #
    cJ
    cA
    cX
    cB
    indif2
    @2
    cJ
    ctop
    wcel
    #
    @0
    @6
    cJ
    wcel
    #
    @7
    cJ
    wcel
    @1
    @8
    @0
    cB
    cJ
    cldrcl
    adantl
    @0
    @1
    simpl
    @1
    @9
    @0
    cB
    cJ
    cX
    iscld.1
    cldopn
    adantl
    cA
    @6
    cJ
    inopn
    syl3anc
    syl5eqelr
    eqeltrrd
end
