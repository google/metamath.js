include "wcel.mm"
include "wceq.mm"
include "ctg.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "cfne.mm"
include "wbr.mm"
include "cvv.mm"
include "wb.mm"
include "cuni.mm"
include "simpr.mm"
include "3eqtr3g.mm"
include "uniexg.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "uniexb.mm"
include "sylibr.mm"
include "simpl.mm"
include "tgss3.mm"
include "syl2anc.mm"
include "pm5.32da.mm"
include "isfne4.mm"
include "syl6rbbr.mm"

theorem isfne4b
  let cA: class A
  let cB: class B
  let cV: class V
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  assume isfne.1: |- X = U. A
  assume isfne.2: |- Y = U. B


  assert |- ( B e. V -> ( A Fne B <-> ( X = Y /\ ( topGen ` A ) C_ ( topGen ` B ) ) ) )

  proof
    cB
    cV
    wcel
    #
    cX
    cY
    wceq
    #
    cA
    ctg
    cfv
    cB
    ctg
    cfv
    #
    wss
    #
    wa
    @1
    cA
    @2
    wss
    #
    wa
    cA
    cB
    cfne
    wbr
    @0
    @1
    @3
    @4
    @0
    @1
    wa
    #
    cA
    cvv
    wcel
    #
    @0
    @3
    @4
    wb
    @5
    cA
    cuni
    #
    cvv
    wcel
    @6
    @5
    @7
    cB
    cuni
    #
    cvv
    @5
    cX
    cY
    @7
    @8
    @0
    @1
    simpr
    isfne.1
    isfne.2
    3eqtr3g
    @0
    @8
    cvv
    wcel
    @1
    cB
    cV
    uniexg
    adantr
    eqeltrd
    cA
    uniexb
    sylibr
    @0
    @1
    simpl
    cA
    cB
    cvv
    cV
    tgss3
    syl2anc
    pm5.32da
    cA
    cB
    cX
    cY
    isfne.1
    isfne.2
    isfne4
    syl6rbbr
end
