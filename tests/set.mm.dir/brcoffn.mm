include "ccom.mm"
include "wfn.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "wf.mm"
include "fnfco.mm"
include "syl2anc.mm"
include "simpl.mm"
include "simpr.mm"
include "syl.mm"
include "fnbr.mm"
include "3jca.mm"
include "mpdan.mm"
include "wceq.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "fvco3.mm"
include "wb.mm"
include "fnbrfvb.mm"
include "3adant1.mm"
include "mpbird.mm"
include "eqtr3d.mm"
include "eqid.mm"
include "jctil.mm"
include "ffnd.mm"
include "ffvelrnd.mm"
include "anbi12d.mm"
include "mpbid.mm"

theorem brcoffn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  let cY: class Y
  assume brcoffn.c: |- ( ph -> C Fn Y )
  assume brcoffn.d: |- ( ph -> D : X --> Y )
  assume brcoffn.r: |- ( ph -> A ( C o. D ) B )


  assert |- ( ph -> ( A D ( D ` A ) /\ ( D ` A ) C B ) )

  proof
    wph
    wph
    cC
    cD
    ccom
    #
    cX
    wfn
    #
    cA
    cX
    wcel
    #
    w3a
    #
    cA
    cA
    cD
    cfv
    #
    cD
    wbr
    #
    @4
    cB
    cC
    wbr
    #
    wa
    #
    wph
    @1
    @3
    wph
    cC
    cY
    wfn
    #
    cX
    cY
    cD
    wf
    #
    @1
    brcoffn.c
    brcoffn.d
    cY
    cX
    cC
    cD
    fnfco
    syl2anc
    wph
    @1
    wa
    #
    wph
    @1
    @2
    wph
    @1
    simpl
    #
    wph
    @1
    simpr
    #
    @10
    @1
    cA
    cB
    @0
    wbr
    #
    @2
    @12
    @10
    wph
    @13
    @11
    brcoffn.r
    syl
    cX
    cA
    cB
    @0
    fnbr
    syl2anc
    3jca
    mpdan
    @3
    @4
    @4
    wceq
    #
    @4
    cC
    cfv
    #
    cB
    wceq
    #
    wa
    @7
    @3
    @16
    @14
    @3
    cA
    @0
    cfv
    #
    @15
    cB
    @3
    @9
    @2
    @17
    @15
    wceq
    wph
    @1
    @9
    @2
    brcoffn.d
    3ad2ant1
    #
    wph
    @1
    @2
    simp3
    #
    cX
    cY
    cA
    cC
    cD
    fvco3
    syl2anc
    @3
    @17
    cB
    wceq
    #
    @13
    wph
    @1
    @13
    @2
    brcoffn.r
    3ad2ant1
    @1
    @2
    @20
    @13
    wb
    wph
    cX
    cA
    cB
    @0
    fnbrfvb
    3adant1
    mpbird
    eqtr3d
    @4
    eqid
    jctil
    @3
    @14
    @5
    @16
    @6
    @3
    cD
    cX
    wfn
    @2
    @14
    @5
    wb
    @3
    cX
    cY
    cD
    @18
    ffnd
    @19
    cX
    cA
    @4
    cD
    fnbrfvb
    syl2anc
    @3
    @8
    @4
    cY
    wcel
    @16
    @6
    wb
    wph
    @1
    @8
    @2
    brcoffn.c
    3ad2ant1
    @3
    cX
    cY
    cA
    cD
    @18
    @19
    ffvelrnd
    cY
    @4
    cB
    cC
    fnbrfvb
    syl2anc
    anbi12d
    mpbid
    syl
end
