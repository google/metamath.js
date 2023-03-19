include "wrex.mm"
include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "sbcrexgOLD.mm"
include "ax-mp.mm"
include "sbcbii.mm"
include "bitri.mm"

theorem 2sbcrexOLD
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume 2sbcrex.1: |- A e. _V
  assume 2sbcrex.2: |- B e. _V

  disjoint A c
  disjoint B c
  disjoint C b
  disjoint a c
  disjoint b c
  disjoint C a
  assert |- ( [. A / a ]. [. B / b ]. E. c e. C ph <-> E. c e. C [. A / a ]. [. B / b ]. ph )

  proof
    wph
    vc
    cC
    wrex
    vb
    cB
    wsbc
    #
    va
    cA
    wsbc
    wph
    vb
    cB
    wsbc
    #
    vc
    cC
    wrex
    #
    va
    cA
    wsbc
    #
    @1
    va
    cA
    wsbc
    vc
    cC
    wrex
    #
    @0
    @2
    va
    cA
    cB
    cvv
    wcel
    @0
    @2
    wb
    2sbcrex.2
    wph
    vb
    vc
    cB
    cC
    cvv
    sbcrexgOLD
    ax-mp
    sbcbii
    cA
    cvv
    wcel
    @3
    @4
    wb
    2sbcrex.1
    @1
    va
    vc
    cA
    cC
    cvv
    sbcrexgOLD
    ax-mp
    bitri
end
