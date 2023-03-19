include "wfo.mm"
include "wf.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "dffo4.mm"
include "rexex.mm"
include "ralimi.mm"
include "anim2i.mm"
include "wcel.mm"
include "wfn.mm"
include "wi.mm"
include "ffn.mm"
include "fnbr.mm"
include "ex.mm"
include "syl.mm"
include "ancrd.mm"
include "eximdv.mm"
include "df-rex.mm"
include "syl6ibr.mm"
include "ralimdv.mm"
include "imdistani.mm"
include "impbii.mm"
include "bitri.mm"

theorem dffo5
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B f
  disjoint B g
  disjoint B z
  disjoint F z
  assert |- ( F : A -onto-> B <-> ( F : A --> B /\ A. y e. B E. x x F y ) )

  proof
    cA
    cB
    cF
    wfo
    cA
    cB
    cF
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    wbr
    #
    vx
    cA
    wrex
    #
    vy
    cB
    wral
    #
    wa
    #
    @0
    @3
    vx
    wex
    #
    vy
    cB
    wral
    #
    wa
    #
    vx
    vy
    cA
    cB
    cF
    dffo4
    @6
    @9
    @5
    @8
    @0
    @4
    @7
    vy
    cB
    @3
    vx
    cA
    rexex
    ralimi
    anim2i
    @0
    @8
    @5
    @0
    @7
    @4
    vy
    cB
    @0
    @7
    @1
    cA
    wcel
    #
    @3
    wa
    #
    vx
    wex
    @4
    @0
    @3
    @11
    vx
    @0
    @3
    @10
    @0
    cF
    cA
    wfn
    #
    @3
    @10
    wi
    cA
    cB
    cF
    ffn
    @12
    @3
    @10
    cA
    @1
    @2
    cF
    fnbr
    ex
    syl
    ancrd
    eximdv
    @3
    vx
    cA
    df-rex
    syl6ibr
    ralimdv
    imdistani
    impbii
    bitri
end
