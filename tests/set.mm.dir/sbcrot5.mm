include "wsbc.mm"
include "sbcrot3.mm"
include "sbcbii.mm"
include "bitri.mm"

theorem sbcrot5
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let ve: setvar e
  let cE: class E
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d

  disjoint A b
  disjoint A c
  disjoint B a
  disjoint C a
  disjoint a c
  disjoint a b
  disjoint A d
  disjoint A e
  disjoint D a
  disjoint E a
  disjoint a e
  disjoint a d
  assert |- ( [. A / a ]. [. B / b ]. [. C / c ]. [. D / d ]. [. E / e ]. ph <-> [. B / b ]. [. C / c ]. [. D / d ]. [. E / e ]. [. A / a ]. ph )

  proof
    wph
    ve
    cE
    wsbc
    vd
    cD
    wsbc
    #
    vc
    cC
    wsbc
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
    vc
    cC
    wsbc
    #
    vb
    cB
    wsbc
    wph
    va
    cA
    wsbc
    ve
    cE
    wsbc
    vd
    cD
    wsbc
    #
    vc
    cC
    wsbc
    #
    vb
    cB
    wsbc
    @0
    cA
    cB
    cC
    va
    vb
    vc
    sbcrot3
    @2
    @4
    vb
    cB
    @1
    @3
    vc
    cC
    wph
    cA
    cD
    cE
    va
    vd
    ve
    sbcrot3
    sbcbii
    sbcbii
    bitri
end
