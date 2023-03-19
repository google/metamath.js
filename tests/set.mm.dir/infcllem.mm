include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "ccnv.mm"
include "vex.mm"
include "brcnv.mm"
include "bicomi.mm"
include "notbii.mm"
include "ralbii.mm"
include "rexbii.mm"
include "imbi12i.mm"
include "anbi12i.mm"
include "sylib.mm"

theorem infcllem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  assume infcl.1: |- ( ph -> R Or A )
  assume infcl.2: |- ( ph -> E. x e. A ( A. y e. B -. y R x /\ A. y e. A ( x R y -> E. z e. B z R y ) ) )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint R x
  disjoint R y
  disjoint R z
  assert |- ( ph -> E. x e. A ( A. y e. B -. x `' R y /\ A. y e. A ( y `' R x -> E. z e. B y `' R z ) ) )

  proof
    wph
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    @1
    @0
    cR
    wbr
    #
    vz
    cv
    #
    @0
    cR
    wbr
    #
    vz
    cB
    wrex
    #
    wi
    #
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    wrex
    @1
    @0
    cR
    ccnv
    #
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    @0
    @1
    @12
    wbr
    #
    @0
    @6
    @12
    wbr
    #
    vz
    cB
    wrex
    #
    wi
    #
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    wrex
    infcl.2
    @11
    @21
    vx
    cA
    @4
    @15
    @10
    @20
    @3
    @14
    vy
    cB
    @2
    @13
    @13
    @2
    @1
    @0
    cR
    vx
    vex
    #
    vy
    vex
    #
    brcnv
    bicomi
    notbii
    ralbii
    @9
    @19
    vy
    cA
    @5
    @16
    @8
    @18
    @16
    @5
    @0
    @1
    cR
    @23
    @22
    brcnv
    bicomi
    @7
    @17
    vz
    cB
    @17
    @7
    @0
    @6
    cR
    @23
    vz
    vex
    brcnv
    bicomi
    rexbii
    imbi12i
    ralbii
    anbi12i
    rexbii
    sylib
end
