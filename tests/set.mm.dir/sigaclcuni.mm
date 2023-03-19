include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "w3a.mm"
include "ciun.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "dfiun2g.mm"
include "3ad2ant2.mm"
include "cpw.mm"
include "simp1.mm"
include "wss.mm"
include "wa.mm"
include "r19.29.mm"
include "simpr.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "rexlimivw.mm"
include "syl.mm"
include "ex.mm"
include "abssdv.mm"
include "wb.mm"
include "elpw2g.mm"
include "mpbird.mm"
include "abrexctf.mm"
include "3ad2ant3.mm"
include "sigaclcu.mm"
include "syl3anc.mm"

theorem sigaclcuni
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let vz: setvar z
  let vo: setvar o
  let vs: setvar s
  let vx: setvar x
  assume sigaclcuni.1: |- F/_ k A

  disjoint S k
  disjoint A z
  disjoint B z
  disjoint k z
  disjoint S z
  disjoint o s
  disjoint o x
  disjoint S o
  disjoint s x
  disjoint S s
  disjoint S x
  disjoint A x
  assert |- ( ( S e. U. ran sigAlgebra /\ A. k e. A B e. S /\ A ~<_ _om ) -> U_ k e. A B e. S )

  proof
    cS
    csiga
    crn
    cuni
    #
    wcel
    #
    cB
    cS
    wcel
    #
    vk
    cA
    wral
    #
    cA
    com
    cdom
    wbr
    #
    w3a
    #
    vk
    cA
    cB
    ciun
    #
    vz
    cv
    #
    cB
    wceq
    #
    vk
    cA
    wrex
    #
    vz
    cab
    #
    cuni
    #
    cS
    @3
    @1
    @6
    @11
    wceq
    @4
    vk
    vz
    cA
    cB
    cS
    dfiun2g
    3ad2ant2
    @5
    @1
    @10
    cS
    cpw
    wcel
    #
    @10
    com
    cdom
    wbr
    #
    @11
    cS
    wcel
    @1
    @3
    @4
    simp1
    #
    @5
    @12
    @10
    cS
    wss
    #
    @3
    @1
    @15
    @4
    @3
    @9
    vz
    cS
    @3
    @9
    @7
    cS
    wcel
    #
    @3
    @9
    wa
    @2
    @8
    wa
    #
    vk
    cA
    wrex
    @16
    @2
    @8
    vk
    cA
    r19.29
    @17
    @16
    vk
    cA
    @17
    @7
    cB
    cS
    @2
    @8
    simpr
    @2
    @8
    simpl
    eqeltrd
    rexlimivw
    syl
    ex
    abssdv
    3ad2ant2
    @5
    @1
    @12
    @15
    wb
    @14
    @10
    cS
    @0
    elpw2g
    syl
    mpbird
    @4
    @1
    @13
    @3
    vk
    vz
    cA
    cB
    sigaclcuni.1
    abrexctf
    3ad2ant3
    @10
    cS
    sigaclcu
    syl3anc
    eqeltrd
end
