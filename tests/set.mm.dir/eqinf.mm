include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "w3a.mm"
include "cinf.mm"
include "wceq.mm"
include "wa.mm"
include "ccnv.mm"
include "csup.mm"
include "df-inf.mm"
include "wor.mm"
include "cnvso.mm"
include "sylib.mm"
include "eqsup.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "brcnvg.mm"
include "bicomd.mm"
include "mpan2.mm"
include "notbid.mm"
include "ralbidv.mm"
include "mpan.mm"
include "brcnv.mm"
include "a1i.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "anbi12d.mm"
include "pm5.32i.mm"
include "3anass.mm"
include "3bitr4i.mm"
include "biimpi.mm"
include "impel.mm"
include "syl5eq.mm"
include "ex.mm"

theorem eqinf
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume infexd.1: |- ( ph -> R Or A )

  disjoint C y
  disjoint C z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint R y
  disjoint R z
  assert |- ( ph -> ( ( C e. A /\ A. y e. B -. y R C /\ A. y e. A ( C R y -> E. z e. B z R y ) ) -> inf ( B , A , R ) = C ) )

  proof
    wph
    cC
    cA
    wcel
    #
    vy
    cv
    #
    cC
    cR
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    cC
    @1
    cR
    wbr
    #
    vz
    cv
    #
    @1
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
    w3a
    #
    cB
    cA
    cR
    cinf
    #
    cC
    wceq
    wph
    @11
    wa
    @12
    cB
    cA
    cR
    ccnv
    #
    csup
    #
    cC
    cB
    cA
    cR
    df-inf
    wph
    @0
    cC
    @1
    @13
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    @1
    cC
    @13
    wbr
    #
    @1
    @6
    @13
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
    w3a
    #
    @14
    cC
    wceq
    @11
    wph
    vy
    vz
    cA
    cB
    cC
    @13
    wph
    cA
    cR
    wor
    cA
    @13
    wor
    infexd.1
    cA
    cR
    cnvso
    sylib
    eqsup
    @11
    @23
    @0
    @4
    @10
    wa
    #
    wa
    @0
    @17
    @22
    wa
    #
    wa
    @11
    @23
    @0
    @24
    @25
    @0
    @4
    @17
    @10
    @22
    @0
    @3
    @16
    vy
    cB
    @0
    @2
    @15
    @0
    @1
    cvv
    wcel
    #
    @2
    @15
    wb
    vy
    vex
    #
    @0
    @26
    wa
    @15
    @2
    cC
    @1
    cA
    cvv
    cR
    brcnvg
    bicomd
    mpan2
    notbid
    ralbidv
    @0
    @9
    @21
    vy
    cA
    @0
    @5
    @18
    @8
    @20
    @0
    @18
    @5
    @26
    @0
    @18
    @5
    wb
    @27
    @1
    cC
    cvv
    cA
    cR
    brcnvg
    mpan
    bicomd
    @0
    @7
    @19
    vz
    cB
    @0
    @19
    @7
    @19
    @7
    wb
    @0
    @1
    @6
    cR
    @27
    vz
    vex
    brcnv
    a1i
    bicomd
    rexbidv
    imbi12d
    ralbidv
    anbi12d
    pm5.32i
    @0
    @4
    @10
    3anass
    @0
    @17
    @22
    3anass
    3bitr4i
    biimpi
    impel
    syl5eq
    ex
end
