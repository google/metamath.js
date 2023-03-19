include "ccnv.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "wrel.mm"
include "wer.mm"
include "errel.mm"
include "syl.mm"
include "brrelex12.mm"
include "syl2anc.mm"
include "brcnvg.mm"
include "ancoms.mm"
include "mpbird.mm"
include "ccom.mm"
include "cun.mm"
include "wss.mm"
include "cdm.mm"
include "wceq.mm"
include "df-er.mm"
include "simp3bi.mm"
include "unssad.mm"
include "ssbrd.mm"
include "mpd.mm"

theorem ersym
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  assume ersym.1: |- ( ph -> R Er X )
  assume ersym.2: |- ( ph -> A R B )


  assert |- ( ph -> B R A )

  proof
    wph
    cB
    cA
    cR
    ccnv
    #
    wbr
    #
    cB
    cA
    cR
    wbr
    wph
    @1
    cA
    cB
    cR
    wbr
    #
    ersym.2
    wph
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    #
    @1
    @2
    wb
    #
    wph
    cR
    wrel
    #
    @2
    @5
    wph
    cX
    cR
    wer
    #
    @7
    ersym.1
    cX
    cR
    errel
    syl
    ersym.2
    cA
    cB
    cR
    brrelex12
    syl2anc
    @4
    @3
    @6
    cB
    cA
    cvv
    cvv
    cR
    brcnvg
    ancoms
    syl
    mpbird
    wph
    @0
    cR
    cB
    cA
    wph
    @0
    cR
    cR
    ccom
    #
    cR
    wph
    @8
    @0
    @9
    cun
    cR
    wss
    #
    ersym.1
    @8
    @7
    cR
    cdm
    cX
    wceq
    @10
    cX
    cR
    df-er
    simp3bi
    syl
    unssad
    ssbrd
    mpd
end
