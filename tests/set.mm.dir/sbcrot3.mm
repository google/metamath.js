include "wsbc.mm"
include "sbccom.mm"
include "sbcbii.mm"
include "bitri.mm"

theorem sbcrot3
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
  disjoint a c
  disjoint a b
  assert |- ( [. A / a ]. [. B / b ]. [. C / c ]. ph <-> [. B / b ]. [. C / c ]. [. A / a ]. ph )

  proof
    wph
    vc
    cC
    wsbc
    #
    vb
    cB
    wsbc
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
    wsbc
    wph
    va
    cA
    wsbc
    vc
    cC
    wsbc
    #
    vb
    cB
    wsbc
    @0
    va
    vb
    cA
    cB
    sbccom
    @1
    @2
    vb
    cB
    wph
    va
    vc
    cA
    cC
    sbccom
    sbcbii
    bitri
end
