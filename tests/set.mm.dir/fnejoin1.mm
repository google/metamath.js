include "wcel.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "c0.mm"
include "csn.mm"
include "cif.mm"
include "cfne.mm"
include "ctg.mm"
include "cfv.mm"
include "wss.mm"
include "wbr.mm"
include "elssuni.mm"
include "3ad2ant3.mm"
include "unissd.mm"
include "cpw.mm"
include "eqimss2.mm"
include "sspwuni.mm"
include "sylibr.mm"
include "ralimi.mm"
include "3ad2ant2.mm"
include "unissb.mm"
include "sylib.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "rspccva.mm"
include "3adant1.mm"
include "sseqtrd.mm"
include "eqssd.mm"
include "cvv.mm"
include "pwexg.mm"
include "3ad2ant1.mm"
include "ssexd.mm"
include "bastg.mm"
include "syl.mm"
include "sstrd.mm"
include "eqid.mm"
include "isfne4.mm"
include "sylanbrc.mm"
include "wne.mm"
include "ne0i.mm"
include "ifnefalse.mm"
include "breqtrrd.mm"

theorem fnejoin1
  let vy: setvar y
  let cA: class A
  let cS: class S
  let cV: class V
  let cX: class X
  let vt: setvar t
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let cT: class T

  disjoint A y
  disjoint S y
  disjoint X y
  disjoint t y
  disjoint A t
  disjoint j k
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint S j
  disjoint k t
  disjoint k x
  disjoint k y
  disjoint S k
  disjoint t x
  disjoint S t
  disjoint x y
  disjoint S x
  disjoint V j
  disjoint V k
  disjoint V t
  disjoint V x
  disjoint X j
  disjoint X k
  disjoint X t
  disjoint X x
  disjoint T t
  disjoint T x
  assert |- ( ( X e. V /\ A. y e. S X = U. y /\ A e. S ) -> A Fne if ( S = (/) , { X } , U. S ) )

  proof
    cX
    cV
    wcel
    #
    cX
    vy
    cv
    #
    cuni
    #
    wceq
    #
    vy
    cS
    wral
    #
    cA
    cS
    wcel
    #
    w3a
    #
    cA
    cS
    cuni
    #
    cS
    c0
    wceq
    cX
    csn
    #
    @7
    cif
    #
    cfne
    @6
    cA
    cuni
    #
    @7
    cuni
    #
    wceq
    cA
    @7
    ctg
    cfv
    #
    wss
    cA
    @7
    cfne
    wbr
    @6
    @10
    @11
    @6
    cA
    @7
    @5
    @0
    cA
    @7
    wss
    @4
    cA
    cS
    elssuni
    3ad2ant3
    #
    unissd
    @6
    @11
    cX
    @10
    @6
    @7
    cX
    cpw
    #
    wss
    #
    @11
    cX
    wss
    @6
    @1
    @14
    wss
    #
    vy
    cS
    wral
    #
    @15
    @4
    @0
    @17
    @5
    @3
    @16
    vy
    cS
    @3
    @2
    cX
    wss
    @16
    @2
    cX
    eqimss2
    @1
    cX
    sspwuni
    sylibr
    ralimi
    3ad2ant2
    vy
    cS
    @14
    unissb
    sylibr
    #
    @7
    cX
    sspwuni
    sylib
    @4
    @5
    cX
    @10
    wceq
    #
    @0
    @3
    @19
    vy
    cA
    cS
    @1
    cA
    wceq
    @2
    @10
    cX
    @1
    cA
    unieq
    eqeq2d
    rspccva
    3adant1
    sseqtrd
    eqssd
    @6
    cA
    @7
    @12
    @13
    @6
    @7
    cvv
    wcel
    @7
    @12
    wss
    @6
    @7
    @14
    cvv
    @0
    @4
    @14
    cvv
    wcel
    @5
    cX
    cV
    pwexg
    3ad2ant1
    @18
    ssexd
    @7
    cvv
    bastg
    syl
    sstrd
    cA
    @7
    @10
    @11
    @10
    eqid
    @11
    eqid
    isfne4
    sylanbrc
    @6
    cS
    c0
    wne
    #
    @9
    @7
    wceq
    @5
    @0
    @20
    @4
    cS
    cA
    ne0i
    3ad2ant3
    cS
    c0
    @8
    @7
    ifnefalse
    syl
    breqtrrd
end
