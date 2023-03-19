include "cdm.mm"
include "wcel.mm"
include "cec.mm"
include "c0.mm"
include "wne.mm"
include "neeq1d.mm"
include "ecdmn0.mm"
include "3bitr4g.mm"
include "wer.mm"
include "wceq.mm"
include "erdm.mm"
include "syl.mm"
include "eleq2d.mm"
include "3bitr3d.mm"

theorem ereldm
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  assume ereldm.1: |- ( ph -> R Er X )
  assume ereldm.2: |- ( ph -> [ A ] R = [ B ] R )


  assert |- ( ph -> ( A e. X <-> B e. X ) )

  proof
    wph
    cA
    cR
    cdm
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cA
    cX
    wcel
    cB
    cX
    wcel
    wph
    cA
    cR
    cec
    #
    c0
    wne
    cB
    cR
    cec
    #
    c0
    wne
    @1
    @2
    wph
    @3
    @4
    c0
    ereldm.2
    neeq1d
    cA
    cR
    ecdmn0
    cB
    cR
    ecdmn0
    3bitr4g
    wph
    @0
    cX
    cA
    wph
    cX
    cR
    wer
    @0
    cX
    wceq
    ereldm.1
    cX
    cR
    erdm
    syl
    #
    eleq2d
    wph
    @0
    cX
    cB
    @5
    eleq2d
    3bitr3d
end
