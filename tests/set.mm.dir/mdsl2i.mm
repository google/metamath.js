include "cin.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "wi.mm"
include "cch.mm"
include "wral.mm"
include "wceq.mm"
include "cmd.mm"
include "wbr.mm"
include "wcel.mm"
include "chub2i.mm"
include "sstr.mm"
include "mpan2.mm"
include "pm4.71ri.mm"
include "anbi2i.mm"
include "anass.mm"
include "bitr4i.mm"
include "imbi1i.mm"
include "wb.mm"
include "chub1.mm"
include "iba.mm"
include "ssin.mm"
include "syl6bb.mm"
include "syl5ibcom.mm"
include "chub2.mm"
include "mpan.mm"
include "ssrin.mm"
include "syl.mm"
include "jctird.mm"
include "chjcl.mm"
include "chincl.mm"
include "chincli.mm"
include "chlub.mm"
include "mp3an2.mm"
include "mpdan.mm"
include "sylibd.mm"
include "eqss.mm"
include "rbaib.mm"
include "syl6.mm"
include "adantld.mm"
include "pm5.74d.mm"
include "syl5rbbr.mm"
include "impexp.mm"
include "ralbiia.mm"
include "mdsl1i.mm"
include "bitr2i.mm"

theorem mdsl2i
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume mdsl.1: |- A e. CH
  assume mdsl.2: |- B e. CH

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A MH B <-> A. x e. CH ( ( ( A i^i B ) C_ x /\ x C_ B ) -> ( ( x vH A ) i^i B ) C_ ( x vH ( A i^i B ) ) ) )

  proof
    cA
    cB
    cin
    #
    vx
    cv
    #
    wss
    #
    @1
    cB
    wss
    #
    wa
    #
    @1
    cA
    chj
    co
    #
    cB
    cin
    #
    @1
    @0
    chj
    co
    #
    wss
    #
    wi
    #
    vx
    cch
    wral
    @2
    @1
    cA
    cB
    chj
    co
    #
    wss
    #
    wa
    #
    @3
    @6
    @7
    wceq
    #
    wi
    wi
    #
    vx
    cch
    wral
    cA
    cB
    cmd
    wbr
    @9
    @14
    vx
    cch
    @1
    cch
    wcel
    #
    @9
    @12
    @3
    wa
    #
    @13
    wi
    #
    @14
    @17
    @4
    @13
    wi
    @15
    @9
    @4
    @16
    @13
    @4
    @2
    @11
    @3
    wa
    #
    wa
    @16
    @3
    @18
    @2
    @3
    @11
    @3
    cB
    @10
    wss
    @11
    cB
    cA
    mdsl.2
    mdsl.1
    chub2i
    @1
    cB
    @10
    sstr
    mpan2
    pm4.71ri
    anbi2i
    @2
    @11
    @3
    anass
    bitr4i
    imbi1i
    @15
    @4
    @13
    @8
    @15
    @3
    @13
    @8
    wb
    #
    @2
    @15
    @3
    @7
    @6
    wss
    #
    @19
    @15
    @3
    @1
    @6
    wss
    #
    @0
    @6
    wss
    #
    wa
    #
    @20
    @15
    @3
    @21
    @22
    @15
    @1
    @5
    wss
    #
    @3
    @21
    @15
    cA
    cch
    wcel
    #
    @24
    mdsl.1
    @1
    cA
    chub1
    mpan2
    @3
    @24
    @24
    @3
    wa
    @21
    @3
    @24
    iba
    @1
    @5
    cB
    ssin
    syl6bb
    syl5ibcom
    @15
    cA
    @5
    wss
    #
    @22
    @25
    @15
    @26
    mdsl.1
    cA
    @1
    chub2
    mpan
    cA
    @5
    cB
    ssrin
    syl
    jctird
    @15
    @6
    cch
    wcel
    #
    @23
    @20
    wb
    #
    @15
    @5
    cch
    wcel
    #
    @27
    @15
    @25
    @29
    mdsl.1
    @1
    cA
    chjcl
    mpan2
    @29
    cB
    cch
    wcel
    @27
    mdsl.2
    @5
    cB
    chincl
    mpan2
    syl
    @15
    @0
    cch
    wcel
    @27
    @28
    cA
    cB
    mdsl.1
    mdsl.2
    chincli
    @1
    @0
    @6
    chlub
    mp3an2
    mpdan
    sylibd
    @13
    @8
    @20
    @6
    @7
    eqss
    rbaib
    syl6
    adantld
    pm5.74d
    syl5rbbr
    @12
    @3
    @13
    impexp
    syl6bb
    ralbiia
    vx
    cA
    cB
    mdsl.1
    mdsl.2
    mdsl1i
    bitr2i
end
