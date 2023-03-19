include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "cconn.mm"
include "cpw.mm"
include "crab.mm"
include "cuni.mm"
include "wrex.mm"
include "csn.mm"
include "wss.mm"
include "simpr.mm"
include "snssd.mm"
include "snex.mm"
include "elpw.mm"
include "sylibr.mm"
include "snidg.mm"
include "adantl.mm"
include "restsn2.mm"
include "c0.mm"
include "cpr.mm"
include "pwsn.mm"
include "indisconn.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "jca.mm"
include "wceq.mm"
include "eleq2.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "elunirab.mm"
include "syl6eleqr.mm"

theorem conncompid
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cJ: class J
  let cX: class X
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cT: class T
  assume conncomp.2: |- S = U. { x e. ~P X | ( A e. x /\ ( J |`t x ) e. Conn ) }

  disjoint A x
  disjoint J x
  disjoint X x
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B k
  disjoint B x
  disjoint J k
  disjoint J y
  disjoint J z
  disjoint T y
  disjoint X k
  disjoint X y
  disjoint X z
  assert |- ( ( J e. ( TopOn ` X ) /\ A e. X ) -> A e. S )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    cA
    vx
    cv
    #
    wcel
    #
    cJ
    @3
    crest
    co
    #
    cconn
    wcel
    #
    wa
    #
    vx
    cX
    cpw
    #
    crab
    cuni
    #
    cS
    @2
    @4
    @7
    wa
    #
    vx
    @8
    wrex
    #
    cA
    @9
    wcel
    @2
    cA
    csn
    #
    @8
    wcel
    #
    cA
    @12
    wcel
    #
    @14
    cJ
    @12
    crest
    co
    #
    cconn
    wcel
    #
    wa
    #
    @11
    @2
    @12
    cX
    wss
    @13
    @2
    cA
    cX
    @0
    @1
    simpr
    snssd
    @12
    cX
    cA
    snex
    elpw
    sylibr
    @1
    @14
    @0
    cA
    cX
    snidg
    adantl
    #
    @2
    @14
    @16
    @18
    @2
    @15
    @12
    cpw
    #
    cconn
    cA
    cJ
    cX
    restsn2
    @19
    c0
    @12
    cpr
    cconn
    cA
    pwsn
    @12
    indisconn
    eqeltri
    syl6eqel
    jca
    @10
    @14
    @17
    wa
    vx
    @12
    @8
    @3
    @12
    wceq
    #
    @4
    @14
    @7
    @17
    @3
    @12
    cA
    eleq2
    #
    @20
    @4
    @14
    @6
    @16
    @21
    @20
    @5
    @15
    cconn
    @3
    @12
    cJ
    crest
    oveq2
    eleq1d
    anbi12d
    anbi12d
    rspcev
    syl12anc
    @7
    vx
    cA
    @8
    elunirab
    sylibr
    conncomp.2
    syl6eleqr
end
