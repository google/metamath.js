include "cv.mm"
include "wbr.mm"
include "cdm.mm"
include "wcel.mm"
include "wex.mm"
include "wer.mm"
include "wceq.mm"
include "erdm.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "wb.mm"
include "eldmg.mm"
include "mpbid.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "ertr4d.mm"
include "exlimddv.mm"

theorem erref
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cX: class X
  let vx: setvar x
  let cB: class B
  let cC: class C
  assume ersymb.1: |- ( ph -> R Er X )
  assume erref.2: |- ( ph -> A e. X )


  assert |- ( ph -> A R A )

  proof
    wph
    cA
    vx
    cv
    #
    cR
    wbr
    #
    cA
    cA
    cR
    wbr
    vx
    wph
    cA
    cR
    cdm
    #
    wcel
    #
    @1
    vx
    wex
    #
    wph
    cA
    cX
    @2
    erref.2
    wph
    cX
    cR
    wer
    #
    @2
    cX
    wceq
    ersymb.1
    cX
    cR
    erdm
    syl
    eleqtrrd
    wph
    cA
    cX
    wcel
    @3
    @4
    wb
    erref.2
    vx
    cA
    cR
    cX
    eldmg
    syl
    mpbid
    wph
    @1
    wa
    cA
    @0
    cA
    cR
    cX
    wph
    @5
    @1
    ersymb.1
    adantr
    wph
    @1
    simpr
    #
    @6
    ertr4d
    exlimddv
end
