include "wrex.mm"
include "wsbc.mm"
include "sbcrex.mm"
include "sbcbii.mm"
include "bitri.mm"

theorem 2sbcrex
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a
  let vb: setvar b
  let vc: setvar c

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
    @1
    va
    cA
    wsbc
    vc
    cC
    wrex
    @0
    @2
    va
    cA
    wph
    vb
    vc
    cB
    cC
    sbcrex
    sbcbii
    @1
    va
    vc
    cA
    cC
    sbcrex
    bitri
end
