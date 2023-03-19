include "wfun.mm"
include "c0.mm"
include "crn.mm"
include "wnel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "cdm.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "rspcva.mm"
include "wne.mm"
include "nelrnfvne.mm"
include "wex.mm"
include "n0.mm"
include "wb.mm"
include "eleq2.mm"
include "eqcoms.mm"
include "elfvdm.mm"
include "syl6bi.mm"
include "com12.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "syl.mm"
include "3exp.mm"
include "eleq2s.mm"
include "com24.mm"
include "adantr.mm"
include "mpd.mm"
include "ex.mm"
include "com23.mm"
include "com14.mm"
include "3imp.mm"
include "ssrdv.mm"

theorem fveqdmss
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let va: setvar a
  let vb: setvar b
  assume fveqdmss.1: |- D = dom B

  disjoint A x
  disjoint B x
  disjoint D x
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a x
  disjoint b x
  disjoint B a
  disjoint B b
  disjoint D a
  assert |- ( ( Fun B /\ (/) e/ ran B /\ A. x e. D ( A ` x ) = ( B ` x ) ) -> D C_ dom A )

  proof
    cB
    wfun
    #
    c0
    cB
    crn
    wnel
    #
    vx
    cv
    #
    cA
    cfv
    #
    @2
    cB
    cfv
    #
    wceq
    #
    vx
    cD
    wral
    #
    w3a
    va
    cD
    cA
    cdm
    #
    @0
    @1
    @6
    va
    cv
    #
    cD
    wcel
    #
    @8
    @7
    wcel
    #
    wi
    @9
    @1
    @6
    @0
    @10
    @9
    @6
    @1
    @0
    @10
    wi
    #
    @9
    @6
    @1
    @11
    wi
    #
    @9
    @6
    wa
    @8
    cA
    cfv
    #
    @8
    cB
    cfv
    #
    wceq
    #
    @12
    @5
    @15
    vx
    @8
    cD
    vx
    va
    weq
    @3
    @13
    @4
    @14
    @2
    @8
    cA
    fveq2
    @2
    @8
    cB
    fveq2
    eqeq12d
    rspcva
    @9
    @15
    @12
    wi
    @6
    @9
    @0
    @1
    @15
    @10
    @0
    @1
    @15
    @10
    wi
    #
    wi
    #
    wi
    @8
    cB
    cdm
    #
    cD
    @0
    @8
    @18
    wcel
    #
    @17
    @0
    @19
    @1
    @16
    @0
    @19
    @1
    w3a
    @14
    c0
    wne
    #
    @16
    cB
    @8
    c0
    nelrnfvne
    @20
    vb
    cv
    #
    @14
    wcel
    #
    vb
    wex
    @16
    vb
    @14
    n0
    @22
    @16
    vb
    @15
    @22
    @10
    @15
    @22
    @21
    @13
    wcel
    #
    @10
    @22
    @23
    wb
    @14
    @13
    @14
    @13
    @21
    eleq2
    eqcoms
    @21
    @8
    cA
    elfvdm
    syl6bi
    com12
    exlimiv
    sylbi
    syl
    3exp
    com12
    fveqdmss.1
    eleq2s
    com24
    adantr
    mpd
    ex
    com23
    com14
    3imp
    ssrdv
end
