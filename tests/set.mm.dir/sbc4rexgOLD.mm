include "wcel.mm"
include "cvv.mm"
include "wrex.mm"
include "wsbc.mm"
include "wb.mm"
include "elex.mm"
include "sbc2rexgOLD.mm"
include "2rexbidv.mm"
include "bitrd.mm"
include "syl.mm"

theorem sbc4rexgOLD
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let ve: setvar e
  let cE: class E
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d

  disjoint A b
  disjoint A c
  disjoint B a
  disjoint C a
  disjoint a b
  disjoint a c
  disjoint A d
  disjoint A e
  disjoint D a
  disjoint E a
  disjoint a d
  disjoint a e
  assert |- ( A e. V -> ( [. A / a ]. E. b e. B E. c e. C E. d e. D E. e e. E ph <-> E. b e. B E. c e. C E. d e. D E. e e. E [. A / a ]. ph ) )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    wph
    ve
    cE
    wrex
    vd
    cD
    wrex
    #
    vc
    cC
    wrex
    vb
    cB
    wrex
    va
    cA
    wsbc
    #
    wph
    va
    cA
    wsbc
    ve
    cE
    wrex
    vd
    cD
    wrex
    #
    vc
    cC
    wrex
    vb
    cB
    wrex
    #
    wb
    cA
    cV
    elex
    @0
    @2
    @1
    va
    cA
    wsbc
    #
    vc
    cC
    wrex
    vb
    cB
    wrex
    @4
    @1
    cA
    cB
    cC
    cvv
    va
    vb
    vc
    sbc2rexgOLD
    @0
    @5
    @3
    vb
    vc
    cB
    cC
    wph
    cA
    cD
    cE
    cvv
    va
    vd
    ve
    sbc2rexgOLD
    2rexbidv
    bitrd
    syl
end
