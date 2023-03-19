include "wss.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "cconn.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "cpw.mm"
include "crab.mm"
include "cuni.mm"
include "simp1.mm"
include "ctop.mm"
include "cvv.mm"
include "wb.mm"
include "conntop.mm"
include "3ad2ant3.mm"
include "restrcl.mm"
include "simprd.mm"
include "elpwg.mm"
include "3syl.mm"
include "mpbird.mm"
include "3simpc.mm"
include "wceq.mm"
include "eleq2.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "cbvrabv.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "elssuni.mm"
include "syl.mm"
include "syl6sseqr.mm"

theorem conncompss
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cT: class T
  let cJ: class J
  let cX: class X
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  let cB: class B
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
  assert |- ( ( T C_ X /\ A e. T /\ ( J |`t T ) e. Conn ) -> T C_ S )

  proof
    cT
    cX
    wss
    #
    cA
    cT
    wcel
    #
    cJ
    cT
    crest
    co
    #
    cconn
    wcel
    #
    w3a
    #
    cT
    cA
    vx
    cv
    #
    wcel
    #
    cJ
    @5
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
    #
    cuni
    #
    cS
    @4
    cT
    @11
    wcel
    #
    cT
    @12
    wss
    @4
    cT
    @10
    wcel
    #
    @1
    @3
    wa
    #
    @13
    @4
    @14
    @0
    @0
    @1
    @3
    simp1
    @4
    @2
    ctop
    wcel
    #
    cT
    cvv
    wcel
    #
    @14
    @0
    wb
    @3
    @0
    @16
    @1
    @2
    conntop
    3ad2ant3
    @16
    cJ
    cvv
    wcel
    @17
    cT
    cJ
    restrcl
    simprd
    cT
    cX
    cvv
    elpwg
    3syl
    mpbird
    @0
    @1
    @3
    3simpc
    cA
    vy
    cv
    #
    wcel
    #
    cJ
    @18
    crest
    co
    #
    cconn
    wcel
    #
    wa
    #
    @15
    vy
    cT
    @10
    @11
    @18
    cT
    wceq
    #
    @19
    @1
    @21
    @3
    @18
    cT
    cA
    eleq2
    @23
    @20
    @2
    cconn
    @18
    cT
    cJ
    crest
    oveq2
    eleq1d
    anbi12d
    @9
    @22
    vx
    vy
    @10
    @5
    @18
    wceq
    #
    @6
    @19
    @8
    @21
    @5
    @18
    cA
    eleq2
    @24
    @7
    @20
    cconn
    @5
    @18
    cJ
    crest
    oveq2
    eleq1d
    anbi12d
    cbvrabv
    elrab2
    sylanbrc
    cT
    @11
    elssuni
    syl
    conncomp.2
    syl6sseqr
end
