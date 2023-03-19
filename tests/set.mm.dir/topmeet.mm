include "wcel.mm"
include "ctopon.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "cint.mm"
include "cin.mm"
include "cv.mm"
include "wral.mm"
include "crab.mm"
include "cuni.mm"
include "topmtcl.mm"
include "inss2.mm"
include "intss1.mm"
include "syl5ss.mm"
include "rgen.mm"
include "wceq.mm"
include "sseq1.mm"
include "ralbidv.mm"
include "elrab.mm"
include "mpbiran2.mm"
include "sylibr.mm"
include "elssuni.mm"
include "syl.mm"
include "w3a.mm"
include "toponuni.mm"
include "eqimss2.mm"
include "sspwuni.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "ssint.mm"
include "ssind.mm"
include "selpw.mm"
include "rabssdv.mm"
include "sylib.mm"
include "eqssd.mm"

theorem topmeet
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let cV: class V
  let cX: class X
  let vt: setvar t
  let vy: setvar y
  let cA: class A
  let vx: setvar x
  let cT: class T

  disjoint j k
  disjoint S j
  disjoint S k
  disjoint V j
  disjoint V k
  disjoint X j
  disjoint X k
  disjoint t y
  disjoint A t
  disjoint A y
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint k t
  disjoint k x
  disjoint k y
  disjoint t x
  disjoint S t
  disjoint x y
  disjoint S x
  disjoint S y
  disjoint V t
  disjoint V x
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint T t
  disjoint T x
  assert |- ( ( X e. V /\ S C_ ( TopOn ` X ) ) -> ( ~P X i^i |^| S ) = U. { k e. ( TopOn ` X ) | A. j e. S k C_ j } )

  proof
    cX
    cV
    wcel
    cS
    cX
    ctopon
    cfv
    #
    wss
    wa
    #
    cX
    cpw
    #
    cS
    cint
    #
    cin
    #
    vk
    cv
    #
    vj
    cv
    #
    wss
    #
    vj
    cS
    wral
    #
    vk
    @0
    crab
    #
    cuni
    #
    @1
    @4
    @9
    wcel
    #
    @4
    @10
    wss
    @1
    @4
    @0
    wcel
    #
    @11
    cS
    cV
    cX
    topmtcl
    @11
    @12
    @4
    @6
    wss
    #
    vj
    cS
    wral
    #
    @13
    vj
    cS
    @6
    cS
    wcel
    @4
    @3
    @6
    @2
    @3
    inss2
    @6
    cS
    intss1
    syl5ss
    rgen
    @8
    @14
    vk
    @4
    @0
    @5
    @4
    wceq
    @7
    @13
    vj
    cS
    @5
    @4
    @6
    sseq1
    ralbidv
    elrab
    mpbiran2
    sylibr
    @4
    @9
    elssuni
    syl
    @1
    @9
    @4
    cpw
    #
    wss
    @10
    @4
    wss
    @1
    @8
    vk
    @0
    @15
    @1
    @5
    @0
    wcel
    #
    @8
    w3a
    #
    @5
    @4
    wss
    @5
    @15
    wcel
    @17
    @5
    @2
    @3
    @16
    @1
    @5
    @2
    wss
    #
    @8
    @16
    @5
    cuni
    #
    cX
    wss
    #
    @18
    @16
    cX
    @19
    wceq
    @20
    cX
    @5
    toponuni
    @19
    cX
    eqimss2
    syl
    @5
    cX
    sspwuni
    sylibr
    3ad2ant2
    @17
    @8
    @5
    @3
    wss
    @1
    @16
    @8
    simp3
    vj
    @5
    cS
    ssint
    sylibr
    ssind
    vk
    @4
    selpw
    sylibr
    rabssdv
    @9
    @4
    sspwuni
    sylib
    eqssd
end
