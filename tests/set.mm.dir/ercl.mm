include "cdm.mm"
include "wrel.mm"
include "wbr.mm"
include "wcel.mm"
include "wer.mm"
include "errel.mm"
include "syl.mm"
include "releldm.mm"
include "syl2anc.mm"
include "wceq.mm"
include "erdm.mm"
include "eleqtrd.mm"

theorem ercl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  assume ersym.1: |- ( ph -> R Er X )
  assume ersym.2: |- ( ph -> A R B )


  assert |- ( ph -> A e. X )

  proof
    wph
    cA
    cR
    cdm
    #
    cX
    wph
    cR
    wrel
    #
    cA
    cB
    cR
    wbr
    cA
    @0
    wcel
    wph
    cX
    cR
    wer
    #
    @1
    ersym.1
    cX
    cR
    errel
    syl
    ersym.2
    cA
    cB
    cR
    releldm
    syl2anc
    wph
    @2
    @0
    cX
    wceq
    ersym.1
    cX
    cR
    erdm
    syl
    eleqtrd
end
