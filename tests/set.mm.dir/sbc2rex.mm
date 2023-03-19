include "wrex.mm"
include "wsbc.mm"
include "sbcrex.mm"
include "rexbii.mm"
include "bitri.mm"

theorem sbc2rex
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a
  let vb: setvar b
  let vc: setvar c

  disjoint A b
  disjoint A c
  disjoint B a
  disjoint C a
  disjoint a b
  disjoint a c
  assert |- ( [. A / a ]. E. b e. B E. c e. C ph <-> E. b e. B E. c e. C [. A / a ]. ph )

  proof
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
    @0
    va
    cA
    wsbc
    #
    vb
    cB
    wrex
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
    @0
    va
    vb
    cA
    cB
    sbcrex
    @1
    @2
    vb
    cB
    wph
    va
    vc
    cA
    cC
    sbcrex
    rexbii
    bitri
end
