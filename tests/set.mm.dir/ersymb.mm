include "wbr.mm"
include "wa.mm"
include "wer.mm"
include "adantr.mm"
include "simpr.mm"
include "ersym.mm"
include "impbida.mm"

theorem ersymb
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  let vx: setvar x
  let cC: class C
  assume ersymb.1: |- ( ph -> R Er X )


  assert |- ( ph -> ( A R B <-> B R A ) )

  proof
    wph
    cA
    cB
    cR
    wbr
    #
    cB
    cA
    cR
    wbr
    #
    wph
    @0
    wa
    cA
    cB
    cR
    cX
    wph
    cX
    cR
    wer
    #
    @0
    ersymb.1
    adantr
    wph
    @0
    simpr
    ersym
    wph
    @1
    wa
    cB
    cA
    cR
    cX
    wph
    @2
    @1
    ersymb.1
    adantr
    wph
    @1
    simpr
    ersym
    impbida
end
