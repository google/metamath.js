include "crn.mm"
include "cec.mm"
include "csn.mm"
include "cima.mm"
include "df-ec.mm"
include "imassrn.mm"
include "eqsstri.mm"
include "wer.mm"
include "wceq.mm"
include "errn.mm"
include "syl.mm"
include "syl5sseq.mm"

theorem ecss
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cX: class X
  assume ecss.1: |- ( ph -> R Er X )


  assert |- ( ph -> [ A ] R C_ X )

  proof
    wph
    cR
    crn
    #
    cA
    cR
    cec
    #
    cX
    @1
    cR
    cA
    csn
    #
    cima
    @0
    cA
    cR
    df-ec
    cR
    @2
    imassrn
    eqsstri
    wph
    cX
    cR
    wer
    @0
    cX
    wceq
    ecss.1
    cX
    cR
    errn
    syl
    syl5sseq
end
