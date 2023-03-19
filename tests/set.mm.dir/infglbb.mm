include "cinf.mm"
include "wbr.mm"
include "ccnv.mm"
include "csup.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
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
include "suplub2.mm"
include "cvv.mm"
include "vex.mm"
include "sylancl.mm"
include "rexbidv.mm"
include "3bitrd.mm"
include "syl5bb.mm"

theorem infglbb
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
  assume infglbb.3: |- ( ph -> B C_ A )

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
  assert |- ( ( ph /\ C e. A ) -> ( inf ( B , A , R ) R C <-> E. z e. B z R C ) )

  proof
    cB
    cA
    cR
    cinf
    #
    cC
    cR
    wbr
    cB
    cA
    cR
    ccnv
    #
    csup
    #
    cC
    cR
    wbr
    #
    wph
    cC
    cA
    wcel
    #
    wa
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
    @0
    @2
    cC
    cR
    cB
    cA
    cR
    df-inf
    breq1i
    @5
    @3
    cC
    @2
    @1
    wbr
    #
    cC
    @6
    @1
    wbr
    #
    vz
    cB
    wrex
    @8
    @5
    @4
    @2
    cA
    wcel
    #
    @3
    @9
    wb
    wph
    @4
    simpr
    #
    wph
    @11
    @4
    wph
    vx
    vy
    vz
    cA
    cB
    @1
    wph
    cA
    cR
    wor
    cA
    @1
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
    @4
    @11
    wa
    @9
    @3
    cC
    @2
    cA
    cA
    cR
    brcnvg
    bicomd
    syl2anc
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    @1
    @13
    @14
    infglbb.3
    suplub2
    @5
    @10
    @7
    vz
    cB
    @5
    @4
    @6
    cvv
    wcel
    @10
    @7
    wb
    @12
    vz
    vex
    cC
    @6
    cA
    cvv
    cR
    brcnvg
    sylancl
    rexbidv
    3bitrd
    syl5bb
end
