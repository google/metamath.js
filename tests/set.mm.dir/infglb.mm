include "wcel.mm"
include "cinf.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "wa.mm"
include "ccnv.mm"
include "csup.mm"
include "df-inf.mm"
include "breq1i.mm"
include "wb.mm"
include "simpr.mm"
include "wor.mm"
include "cnvso.mm"
include "sylib.mm"
include "infcllem.mm"
include "supcl.mm"
include "adantr.mm"
include "brcnvg.mm"
include "bicomd.mm"
include "syl2anc.mm"
include "syl5bb.mm"
include "suplub.mm"
include "expdimp.mm"
include "cvv.mm"
include "vex.mm"
include "sylancl.mm"
include "rexbidv.mm"
include "sylibd.mm"
include "sylbid.mm"
include "expimpd.mm"

theorem infglb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
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
  disjoint C z
  disjoint ph z
  assert |- ( ph -> ( ( C e. A /\ inf ( B , A , R ) R C ) -> E. z e. B z R C ) )

  proof
    wph
    cC
    cA
    wcel
    #
    cB
    cA
    cR
    cinf
    #
    cC
    cR
    wbr
    #
    vz
    cv
    #
    cC
    cR
    wbr
    #
    vz
    cB
    wrex
    #
    wph
    @0
    wa
    #
    @2
    cC
    cB
    cA
    cR
    ccnv
    #
    csup
    #
    @7
    wbr
    #
    @5
    @2
    @8
    cC
    cR
    wbr
    #
    @6
    @9
    @1
    @8
    cC
    cR
    cB
    cA
    cR
    df-inf
    breq1i
    @6
    @0
    @8
    cA
    wcel
    #
    @10
    @9
    wb
    wph
    @0
    simpr
    #
    wph
    @11
    @0
    wph
    vx
    vy
    vz
    cA
    cB
    @7
    wph
    cA
    cR
    wor
    cA
    @7
    wor
    infcl.1
    cA
    cR
    cnvso
    sylib
    #
    wph
    vx
    vy
    vz
    cA
    cB
    cR
    infcl.1
    infcl.2
    infcllem
    #
    supcl
    adantr
    @0
    @11
    wa
    @9
    @10
    cC
    @8
    cA
    cA
    cR
    brcnvg
    bicomd
    syl2anc
    syl5bb
    @6
    @9
    cC
    @3
    @7
    wbr
    #
    vz
    cB
    wrex
    #
    @5
    wph
    @0
    @9
    @16
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    @7
    @13
    @14
    suplub
    expdimp
    @6
    @15
    @4
    vz
    cB
    @6
    @0
    @3
    cvv
    wcel
    @15
    @4
    wb
    @12
    vz
    vex
    cC
    @3
    cA
    cvv
    cR
    brcnvg
    sylancl
    rexbidv
    sylibd
    sylbid
    expimpd
end
