include "wbr.mm"
include "wa.mm"
include "ccom.mm"
include "cv.mm"
include "wex.mm"
include "cvv.mm"
include "wcel.mm"
include "wrel.mm"
include "wer.mm"
include "errel.mm"
include "syl.mm"
include "simpr.mm"
include "brrelex.mm"
include "syl2an.mm"
include "wceq.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"
include "wb.mm"
include "simpl.mm"
include "brrelex2.mm"
include "brcog.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ex.mm"
include "ccnv.mm"
include "cun.mm"
include "wss.mm"
include "cdm.mm"
include "df-er.mm"
include "simp3bi.mm"
include "unssbd.mm"
include "ssbrd.mm"
include "syld.mm"

theorem ertr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cX: class X
  let vx: setvar x
  assume ersymb.1: |- ( ph -> R Er X )


  assert |- ( ph -> ( ( A R B /\ B R C ) -> A R C ) )

  proof
    wph
    cA
    cB
    cR
    wbr
    #
    cB
    cC
    cR
    wbr
    #
    wa
    #
    cA
    cC
    cR
    cR
    ccom
    #
    wbr
    #
    cA
    cC
    cR
    wbr
    wph
    @2
    @4
    wph
    @2
    wa
    #
    @4
    cA
    vx
    cv
    #
    cR
    wbr
    #
    @6
    cC
    cR
    wbr
    #
    wa
    #
    vx
    wex
    #
    @5
    cB
    cvv
    wcel
    #
    @2
    @10
    wph
    cR
    wrel
    #
    @1
    @11
    @2
    wph
    cX
    cR
    wer
    #
    @12
    ersymb.1
    cX
    cR
    errel
    syl
    #
    @0
    @1
    simpr
    #
    cB
    cC
    cR
    brrelex
    syl2an
    wph
    @2
    simpr
    @9
    @2
    vx
    cB
    cvv
    @6
    cB
    wceq
    @7
    @0
    @8
    @1
    @6
    cB
    cA
    cR
    breq2
    @6
    cB
    cC
    cR
    breq1
    anbi12d
    spcegv
    sylc
    @5
    cA
    cvv
    wcel
    #
    cC
    cvv
    wcel
    #
    @4
    @10
    wb
    wph
    @12
    @0
    @16
    @2
    @14
    @0
    @1
    simpl
    cA
    cB
    cR
    brrelex
    syl2an
    wph
    @12
    @1
    @17
    @2
    @14
    @15
    cB
    cC
    cR
    brrelex2
    syl2an
    vx
    cA
    cC
    cR
    cR
    cvv
    cvv
    brcog
    syl2anc
    mpbird
    ex
    wph
    @3
    cR
    cA
    cC
    wph
    cR
    ccnv
    #
    @3
    cR
    wph
    @13
    @18
    @3
    cun
    cR
    wss
    #
    ersymb.1
    @13
    @12
    cR
    cdm
    cX
    wceq
    @19
    cX
    cR
    df-er
    simp3bi
    syl
    unssbd
    ssbrd
    syld
end
