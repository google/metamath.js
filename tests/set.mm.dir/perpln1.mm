include "cperpg.mm"
include "cfv.mm"
include "cdm.mm"
include "crn.mm"
include "cv.mm"
include "wcel.mm"
include "cs3.mm"
include "crag.mm"
include "wral.mm"
include "cin.mm"
include "wrex.mm"
include "wa.mm"
include "copab.mm"
include "clng.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-perpg.mm"
include "a1i.mm"
include "simpr.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "rexralbidv.mm"
include "opabbidv.mm"
include "cstrkg.mm"
include "elex.mm"
include "syl.mm"
include "cxp.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rnexg.mm"
include "mp1i.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "wss.mm"
include "opabssxp.mm"
include "ssexd.mm"
include "fvmptd.mm"
include "anass.mm"
include "opabbii.mm"
include "syl6eq.mm"
include "dmeqd.mm"
include "dmopabss.mm"
include "syl6eqss.mm"
include "wbr.mm"
include "wrel.mm"
include "relopab.mm"
include "releqd.mm"
include "mpbiri.mm"
include "brrelex12.mm"
include "simpld.mm"
include "simprd.mm"
include "breldmg.mm"
include "syl3anc.mm"
include "sseldd.mm"

theorem perpln1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cG: class G
  let cL: class L
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  assume perpln.l: |- L = ( LineG ` G )
  assume perpln.1: |- ( ph -> G e. TarskiG )
  assume perpln.2: |- ( ph -> A ( perpG ` G ) B )


  assert |- ( ph -> A e. ran L )

  proof
    wph
    cG
    cperpg
    cfv
    #
    cdm
    #
    cL
    crn
    #
    cA
    wph
    @1
    va
    cv
    #
    @2
    wcel
    #
    vb
    cv
    #
    @2
    wcel
    #
    vu
    cv
    vx
    cv
    vv
    cv
    cs3
    #
    cG
    crag
    cfv
    #
    wcel
    #
    vv
    @5
    wral
    #
    vu
    @3
    wral
    vx
    @3
    @5
    cin
    #
    wrex
    #
    wa
    #
    wa
    #
    va
    vb
    copab
    #
    cdm
    @2
    wph
    @0
    @15
    wph
    @0
    @4
    @6
    wa
    #
    @12
    wa
    #
    va
    vb
    copab
    #
    @15
    wph
    vg
    cG
    @3
    vg
    cv
    #
    clng
    cfv
    #
    crn
    #
    wcel
    #
    @5
    @21
    wcel
    #
    wa
    #
    @7
    @19
    crag
    cfv
    #
    wcel
    #
    vv
    @5
    wral
    #
    vu
    @3
    wral
    vx
    @11
    wrex
    #
    wa
    #
    va
    vb
    copab
    #
    @18
    cvv
    cperpg
    cvv
    cperpg
    vg
    cvv
    @30
    cmpt
    wceq
    wph
    vx
    vv
    vu
    vg
    va
    vb
    df-perpg
    a1i
    wph
    @19
    cG
    wceq
    #
    wa
    #
    @29
    @17
    va
    vb
    @32
    @24
    @16
    @28
    @12
    @32
    @22
    @4
    @23
    @6
    @32
    @21
    @2
    @3
    @32
    @20
    cL
    @32
    @20
    cG
    clng
    cfv
    #
    cL
    @32
    @19
    cG
    clng
    wph
    @31
    simpr
    #
    fveq2d
    perpln.l
    syl6eqr
    rneqd
    #
    eleq2d
    @32
    @21
    @2
    @5
    @35
    eleq2d
    anbi12d
    @32
    @27
    @10
    vx
    vu
    @11
    @3
    @32
    @26
    @9
    vv
    @5
    @32
    @25
    @8
    @7
    @32
    @19
    cG
    crag
    @34
    fveq2d
    eleq2d
    ralbidv
    rexralbidv
    anbi12d
    opabbidv
    wph
    cG
    cstrkg
    wcel
    cG
    cvv
    wcel
    perpln.1
    cG
    cstrkg
    elex
    syl
    wph
    @18
    @2
    @2
    cxp
    #
    cvv
    wph
    @2
    cvv
    wcel
    #
    @37
    @36
    cvv
    wcel
    cL
    cvv
    wcel
    @37
    wph
    cL
    @33
    cvv
    perpln.l
    cG
    clng
    fvex
    eqeltri
    cL
    cvv
    rnexg
    mp1i
    #
    @38
    @2
    @2
    cvv
    cvv
    xpexg
    syl2anc
    @18
    @36
    wss
    wph
    @12
    va
    vb
    @2
    @2
    opabssxp
    a1i
    ssexd
    fvmptd
    #
    @17
    @14
    va
    vb
    @4
    @6
    @12
    anass
    opabbii
    syl6eq
    dmeqd
    @13
    va
    vb
    @2
    dmopabss
    syl6eqss
    wph
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    cA
    cB
    @0
    wbr
    #
    cA
    @1
    wcel
    wph
    @40
    @41
    wph
    @0
    wrel
    #
    @42
    @40
    @41
    wa
    wph
    @43
    @18
    wrel
    @17
    va
    vb
    relopab
    wph
    @0
    @18
    @39
    releqd
    mpbiri
    perpln.2
    cA
    cB
    @0
    brrelex12
    syl2anc
    #
    simpld
    wph
    @40
    @41
    @44
    simprd
    perpln.2
    cA
    cB
    cvv
    cvv
    @0
    breldmg
    syl3anc
    sseldd
end
