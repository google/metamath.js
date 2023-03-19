include "wcel.mm"
include "cvv.mm"
include "wrex.mm"
include "wsbc.mm"
include "wb.mm"
include "elex.mm"
include "sbcrexgOLD.mm"
include "rexbidv.mm"
include "bitrd.mm"
include "syl.mm"

theorem sbc2rexgOLD
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c

  disjoint A b
  disjoint A c
  disjoint B a
  disjoint C a
  disjoint a b
  disjoint a c
  assert |- ( A e. V -> ( [. A / a ]. E. b e. B E. c e. C ph <-> E. b e. B E. c e. C [. A / a ]. ph ) )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    wph
    vc
    cC
    wrex
    #
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
    vc
    cC
    wrex
    #
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
    vb
    cB
    wrex
    @4
    @1
    va
    vb
    cA
    cB
    cvv
    sbcrexgOLD
    @0
    @5
    @3
    vb
    cB
    wph
    va
    vc
    cA
    cC
    cvv
    sbcrexgOLD
    rexbidv
    bitrd
    syl
end
