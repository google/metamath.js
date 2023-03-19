include "wbr.mm"
include "cec.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "simpl.mm"
include "ersymb.mm"
include "biimpa.mm"
include "jca.mm"
include "ertr.mm"
include "impl.mm"
include "sylan.mm"
include "impbida.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "adantr.mm"
include "elecg.mm"
include "sylancr.mm"
include "wrel.mm"
include "wer.mm"
include "errel.mm"
include "syl.mm"
include "brrelex2.mm"
include "3bitr4d.mm"
include "eqrdv.mm"
include "erref.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "ereldm.mm"
include "mpbid.mm"
include "ersym.mm"

theorem erth
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  let vx: setvar x
  assume erth.1: |- ( ph -> R Er X )
  assume erth.2: |- ( ph -> A e. X )


  assert |- ( ph -> ( A R B <-> [ A ] R = [ B ] R ) )

  proof
    wph
    cA
    cB
    cR
    wbr
    #
    cA
    cR
    cec
    #
    cB
    cR
    cec
    #
    wceq
    #
    wph
    @0
    wa
    #
    vx
    @1
    @2
    @4
    cA
    vx
    cv
    #
    cR
    wbr
    #
    cB
    @5
    cR
    wbr
    #
    @5
    @1
    wcel
    #
    @5
    @2
    wcel
    #
    @4
    @6
    @7
    @4
    wph
    cB
    cA
    cR
    wbr
    #
    wa
    @6
    @7
    @4
    wph
    @10
    wph
    @0
    simpl
    wph
    @0
    @10
    wph
    cA
    cB
    cR
    cX
    erth.1
    ersymb
    biimpa
    jca
    wph
    @10
    @6
    @7
    wph
    cB
    cA
    @5
    cR
    cX
    erth.1
    ertr
    impl
    sylan
    wph
    @0
    @7
    @6
    wph
    cA
    cB
    @5
    cR
    cX
    erth.1
    ertr
    impl
    impbida
    @4
    @5
    cvv
    wcel
    #
    cA
    cX
    wcel
    #
    @8
    @6
    wb
    vx
    vex
    #
    wph
    @12
    @0
    erth.2
    adantr
    @5
    cA
    cR
    cvv
    cX
    elecg
    sylancr
    @4
    @11
    cB
    cvv
    wcel
    #
    @9
    @7
    wb
    @13
    wph
    cR
    wrel
    #
    @0
    @14
    wph
    cX
    cR
    wer
    #
    @15
    erth.1
    cX
    cR
    errel
    syl
    cA
    cB
    cR
    brrelex2
    sylan
    @5
    cB
    cR
    cvv
    cvv
    elecg
    sylancr
    3bitr4d
    eqrdv
    wph
    @3
    wa
    #
    cB
    cA
    cR
    cX
    wph
    @16
    @3
    erth.1
    adantr
    #
    @17
    cA
    @2
    wcel
    #
    @10
    @17
    cA
    @1
    @2
    @17
    cA
    @1
    wcel
    #
    cA
    cA
    cR
    wbr
    #
    wph
    @21
    @3
    wph
    cA
    cR
    cX
    erth.1
    erth.2
    erref
    adantr
    @17
    @12
    @12
    @20
    @21
    wb
    wph
    @12
    @3
    erth.2
    adantr
    #
    @22
    cA
    cA
    cR
    cX
    cX
    elecg
    syl2anc
    mpbird
    wph
    @3
    simpr
    #
    eleqtrd
    @17
    @12
    cB
    cX
    wcel
    #
    @19
    @10
    wb
    @22
    @17
    @12
    @24
    @22
    @17
    cA
    cB
    cR
    cX
    @18
    @23
    ereldm
    mpbid
    cA
    cB
    cR
    cX
    cX
    elecg
    syl2anc
    mpbid
    ersym
    impbida
end
