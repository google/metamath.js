include "cv.mm"
include "cico.mm"
include "ccom.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "funmpt2.mm"
include "a1i.mm"
include "adantr.mm"
include "simpr.mm"
include "cmpt.mm"
include "dmeqi.mm"
include "cvv.mm"
include "wral.mm"
include "opex.mm"
include "2a1i.mm"
include "ralrimi.mm"
include "dmmptg.mm"
include "syl.mm"
include "eqtr2d.mm"
include "eleqtrd.mm"
include "fvco.mm"
include "syl2anc.mm"
include "fvmpt2.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "eqcomi.mm"
include "3eqtrd.mm"
include "ixpeq2d.mm"

theorem hoi2toco
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cI: class I
  let cX: class X
  let vx: setvar x
  assume hoi2toco.1: |- F/ k ph
  assume hoi2toco.c: |- I = ( k e. X |-> <. ( A ` k ) , ( B ` k ) >. )

  disjoint X k
  disjoint k x
  assert |- ( ph -> X_ k e. X ( ( [,) o. I ) ` k ) = X_ k e. X ( ( A ` k ) [,) ( B ` k ) ) )

  proof
    wph
    vk
    cX
    vk
    cv
    #
    cico
    cI
    ccom
    cfv
    #
    @0
    cA
    cfv
    #
    @0
    cB
    cfv
    #
    cico
    co
    #
    hoi2toco.1
    wph
    @0
    cX
    wcel
    #
    wa
    #
    @1
    @0
    cI
    cfv
    #
    cico
    cfv
    #
    @2
    @3
    cop
    #
    cico
    cfv
    #
    @4
    @6
    cI
    wfun
    #
    @0
    cI
    cdm
    #
    wcel
    @1
    @8
    wceq
    wph
    @11
    @5
    @11
    wph
    vk
    cX
    @9
    cI
    hoi2toco.c
    funmpt2
    a1i
    adantr
    @6
    @0
    cX
    @12
    wph
    @5
    simpr
    #
    wph
    cX
    @12
    wceq
    @5
    wph
    @12
    vk
    cX
    @9
    cmpt
    #
    cdm
    #
    cX
    @12
    @15
    wceq
    wph
    cI
    @14
    hoi2toco.c
    dmeqi
    a1i
    wph
    @9
    cvv
    wcel
    #
    vk
    cX
    wral
    @15
    cX
    wceq
    wph
    @16
    vk
    cX
    hoi2toco.1
    @16
    wph
    @5
    @2
    @3
    opex
    #
    2a1i
    ralrimi
    vk
    cX
    @9
    cvv
    dmmptg
    syl
    eqtr2d
    adantr
    eleqtrd
    @0
    cico
    cI
    fvco
    syl2anc
    @6
    @7
    @9
    cico
    @6
    @5
    @16
    @7
    @9
    wceq
    @13
    @16
    @6
    @17
    a1i
    vk
    cX
    @9
    cvv
    cI
    hoi2toco.c
    fvmpt2
    syl2anc
    fveq2d
    @10
    @4
    wceq
    @6
    @4
    @10
    @2
    @3
    cico
    df-ov
    eqcomi
    a1i
    3eqtrd
    ixpeq2d
end
