include "wbr.mm"
include "cec.mm"
include "wceq.mm"
include "ersymb.mm"
include "erth.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "bitrd.mm"

theorem erth2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  assume erth2.1: |- ( ph -> R Er X )
  assume erth2.2: |- ( ph -> B e. X )


  assert |- ( ph -> ( A R B <-> [ A ] R = [ B ] R ) )

  proof
    wph
    cA
    cB
    cR
    wbr
    cB
    cA
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
    cA
    cB
    cR
    cX
    erth2.1
    ersymb
    wph
    @0
    @2
    @1
    wceq
    @3
    wph
    cB
    cA
    cR
    cX
    erth2.1
    erth2.2
    erth
    @2
    @1
    eqcom
    syl6bb
    bitrd
end
