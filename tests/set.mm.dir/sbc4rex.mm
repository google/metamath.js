include "wrex.mm"
include "wsbc.mm"
include "sbc2rex.mm"
include "2rexbii.mm"
include "bitri.mm"

theorem sbc4rex
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
  disjoint a b
  disjoint a c
  disjoint A d
  disjoint A e
  disjoint D a
  disjoint E a
  disjoint a d
  disjoint a e
  assert |- ( [. A / a ]. E. b e. B E. c e. C E. d e. D E. e e. E ph <-> E. b e. B E. c e. C E. d e. D E. e e. E [. A / a ]. ph )

  proof
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
    @0
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
    @0
    cA
    cB
    cC
    va
    vb
    vc
    sbc2rex
    @1
    @2
    vb
    vc
    cB
    cC
    wph
    cA
    cD
    cE
    va
    vd
    ve
    sbc2rex
    2rexbii
    bitri
end
