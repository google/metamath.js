include "cperpg.mm"
include "cfv.mm"
include "crn.mm"
include "cxp.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cs3.mm"
include "crag.mm"
include "wral.mm"
include "cin.mm"
include "wrex.mm"
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
include "rnss.mm"
include "ax-mp.mm"
include "syl6eqss.mm"
include "rnxpss.mm"
include "syl6ss.mm"
include "wbr.mm"
include "wrel.mm"
include "relopab.mm"
include "releqd.mm"
include "mpbiri.mm"
include "brrelex12.mm"
include "simpld.mm"
include "simprd.mm"
include "brelrng.mm"
include "syl3anc.mm"
include "sseldd.mm"

theorem perpln2
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


  assert |- ( ph -> B e. ran L )

  proof
    wph
    cG
    cperpg
    cfv
    #
    crn
    #
    cL
    crn
    #
    cB
    wph
    @1
    @2
    @2
    cxp
    #
    crn
    #
    @2
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
    wa
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
    @7
    wral
    #
    vu
    @5
    wral
    vx
    @5
    @7
    cin
    #
    wrex
    #
    wa
    #
    va
    vb
    copab
    #
    crn
    #
    @4
    wph
    @0
    @17
    wph
    vg
    cG
    @5
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
    @7
    @21
    wcel
    #
    wa
    #
    @10
    @19
    crag
    cfv
    #
    wcel
    #
    vv
    @7
    wral
    #
    vu
    @5
    wral
    vx
    @14
    wrex
    #
    wa
    #
    va
    vb
    copab
    #
    @17
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
    @16
    va
    vb
    @32
    @24
    @9
    @28
    @15
    @32
    @22
    @6
    @23
    @8
    @32
    @21
    @2
    @5
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
    @7
    @35
    eleq2d
    anbi12d
    @32
    @27
    @13
    vx
    vu
    @14
    @5
    @32
    @26
    @12
    vv
    @7
    @32
    @25
    @11
    @10
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
    @17
    @3
    cvv
    wph
    @2
    cvv
    wcel
    #
    @36
    @3
    cvv
    wcel
    cL
    cvv
    wcel
    @36
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
    @37
    @2
    @2
    cvv
    cvv
    xpexg
    syl2anc
    @17
    @3
    wss
    #
    wph
    @15
    va
    vb
    @2
    @2
    opabssxp
    #
    a1i
    ssexd
    fvmptd
    #
    rneqd
    @38
    @18
    @4
    wss
    @39
    @17
    @3
    rnss
    ax-mp
    syl6eqss
    @2
    @2
    rnxpss
    syl6ss
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
    cB
    @1
    wcel
    wph
    @41
    @42
    wph
    @0
    wrel
    #
    @43
    @41
    @42
    wa
    wph
    @44
    @17
    wrel
    @16
    va
    vb
    relopab
    wph
    @0
    @17
    @40
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
    @41
    @42
    @45
    simprd
    perpln.2
    cA
    cB
    @0
    cvv
    cvv
    brelrng
    syl3anc
    sseldd
end
