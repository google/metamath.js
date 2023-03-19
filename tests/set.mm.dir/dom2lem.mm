include "cmpt.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "wcel.mm"
include "ralrimiv.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylib.mm"
include "wa.mm"
include "imp.mm"
include "fvmpt2.mm"
include "adantll.mm"
include "mpdan.mm"
include "adantrr.mm"
include "nfv.mm"
include "nffvmpt1.mm"
include "nfeq1.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "imbi1d.mm"
include "wb.mm"
include "anbi1d.mm"
include "anidm.mm"
include "syl6bb.mm"
include "fveq2.mm"
include "adantr.mm"
include "biimparc.mm"
include "eqeq12d.mm"
include "ex.mm"
include "sylbird.mm"
include "pm5.74d.mm"
include "bitrd.mm"
include "chvar.mm"
include "adantrl.mm"
include "biimpd.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "nfmpt1.mm"
include "nfcv.mm"
include "dff13f.mm"
include "sylanbrc.mm"

theorem dom2lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vz: setvar z
  assume dom2d.1: |- ( ph -> ( x e. A -> C e. B ) )
  assume dom2d.2: |- ( ph -> ( ( x e. A /\ y e. A ) -> ( C = D <-> x = y ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint D x
  disjoint ph x
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D z
  assert |- ( ph -> ( x e. A |-> C ) : A -1-1-> B )

  proof
    wph
    cA
    cB
    vx
    cA
    cC
    cmpt
    #
    wf
    #
    vx
    cv
    #
    @0
    cfv
    #
    vy
    cv
    #
    @0
    cfv
    #
    wceq
    #
    @2
    @4
    wceq
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    cA
    cB
    @0
    wf1
    wph
    cC
    cB
    wcel
    #
    vx
    cA
    wral
    @1
    wph
    @9
    vx
    cA
    dom2d.1
    ralrimiv
    vx
    cA
    cB
    cC
    @0
    @0
    eqid
    #
    fmpt
    sylib
    wph
    @8
    vx
    vy
    cA
    cA
    wph
    @2
    cA
    wcel
    #
    @4
    cA
    wcel
    #
    wa
    #
    wa
    #
    @6
    cC
    cD
    wceq
    #
    @7
    @14
    @3
    cC
    @5
    cD
    wph
    @11
    @3
    cC
    wceq
    #
    @12
    wph
    @11
    wa
    #
    @9
    @16
    wph
    @11
    @9
    dom2d.1
    imp
    @11
    @9
    @16
    wph
    vx
    cA
    cC
    cB
    @0
    @10
    fvmpt2
    adantll
    mpdan
    #
    adantrr
    wph
    @12
    @5
    cD
    wceq
    #
    @11
    @17
    @16
    wi
    #
    wph
    @12
    wa
    #
    @19
    wi
    #
    vx
    vy
    @21
    @19
    vx
    @21
    vx
    nfv
    vx
    @5
    cD
    vx
    cA
    cC
    @4
    nffvmpt1
    nfeq1
    nfim
    @7
    @20
    @21
    @16
    wi
    @22
    @7
    @17
    @21
    @16
    @7
    @11
    @12
    wph
    @2
    @4
    cA
    eleq1
    #
    anbi2d
    imbi1d
    @7
    @21
    @16
    @19
    @7
    @21
    @14
    @16
    @19
    wb
    #
    @7
    @13
    @12
    wph
    @7
    @13
    @12
    @12
    wa
    @12
    @7
    @11
    @12
    @12
    @23
    anbi1d
    @12
    anidm
    syl6bb
    anbi2d
    @7
    @14
    @24
    @7
    @14
    wa
    @3
    @5
    cC
    cD
    @7
    @6
    @14
    @2
    @4
    @0
    fveq2
    adantr
    @14
    @15
    @7
    wph
    @13
    @15
    @7
    wb
    dom2d.2
    imp
    #
    biimparc
    eqeq12d
    ex
    sylbird
    pm5.74d
    bitrd
    @18
    chvar
    adantrl
    eqeq12d
    @14
    @15
    @7
    @25
    biimpd
    sylbid
    ralrimivva
    vx
    vy
    cA
    cB
    @0
    vx
    cA
    cC
    nfmpt1
    vy
    @0
    nfcv
    dff13f
    sylanbrc
end
