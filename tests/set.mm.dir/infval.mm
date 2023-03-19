include "cinf.mm"
include "ccnv.mm"
include "csup.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "crio.mm"
include "df-inf.mm"
include "wor.mm"
include "cnvso.mm"
include "sylib.mm"
include "supval2.mm"
include "wb.mm"
include "vex.mm"
include "brcnv.mm"
include "a1i.mm"
include "notbid.mm"
include "ralbidv.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "anbi12d.mm"
include "riotabidv.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem infval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  assume infexd.1: |- ( ph -> R Or A )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint R y
  disjoint R z
  disjoint A x
  disjoint B x
  disjoint R x
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint x y
  disjoint x z
  assert |- ( ph -> inf ( B , A , R ) = ( iota_ x e. A ( A. y e. B -. y R x /\ A. y e. A ( x R y -> E. z e. B z R y ) ) ) )

  proof
    wph
    cB
    cA
    cR
    cinf
    cB
    cA
    cR
    ccnv
    #
    csup
    #
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
    @3
    @2
    cR
    wbr
    #
    vz
    cv
    #
    @2
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
    crio
    #
    cB
    cA
    cR
    df-inf
    wph
    @1
    @3
    @2
    @0
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    @2
    @3
    @0
    wbr
    #
    @2
    @8
    @0
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
    crio
    @14
    wph
    vx
    vy
    vz
    cA
    cB
    @0
    wph
    cA
    cR
    wor
    cA
    @0
    wor
    infexd.1
    cA
    cR
    cnvso
    sylib
    supval2
    wph
    @23
    @13
    vx
    cA
    wph
    @17
    @6
    @22
    @12
    wph
    @16
    @5
    vy
    cB
    wph
    @15
    @4
    @15
    @4
    wb
    wph
    @3
    @2
    cR
    vx
    vex
    #
    vy
    vex
    #
    brcnv
    a1i
    notbid
    ralbidv
    wph
    @21
    @11
    vy
    cA
    wph
    @18
    @7
    @20
    @10
    @18
    @7
    wb
    wph
    @2
    @3
    cR
    @25
    @24
    brcnv
    a1i
    wph
    @19
    @9
    vz
    cB
    @19
    @9
    wb
    wph
    @2
    @8
    cR
    @25
    vz
    vex
    brcnv
    a1i
    rexbidv
    imbi12d
    ralbidv
    anbi12d
    riotabidv
    eqtrd
    syl5eq
end
