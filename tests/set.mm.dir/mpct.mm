include "cv.mm"
include "cmap.mm"
include "co.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq1d.mm"
include "cvv.mm"
include "wcel.mm"
include "ctex.mm"
include "syl.mm"
include "mapdm0.mm"
include "cfn.mm"
include "snfi.mm"
include "fict.mm"
include "ax-mp.mm"
include "a1i.mm"
include "eqbrtrd.mm"
include "wss.mm"
include "cdif.mm"
include "wa.mm"
include "cxp.mm"
include "cen.mm"
include "cin.mm"
include "vex.mm"
include "snex.mm"
include "ad2antrr.mm"
include "wn.mm"
include "eldifn.mm"
include "disjsn.mm"
include "sylibr.mm"
include "adantl.mm"
include "ad2antlr.mm"
include "mapunen.mm"
include "syl31anc.mm"
include "simpr.mm"
include "mapsnend.mm"
include "endomtr.mm"
include "syl2anc.mm"
include "xpct.mm"
include "ex.mm"
include "findcard2d.mm"

theorem mpct
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume mpct.a: |- ( ph -> A ~<_ _om )
  assume mpct.b: |- ( ph -> B e. Fin )


  assert |- ( ph -> ( A ^m B ) ~<_ _om )

  proof
    wph
    cA
    vx
    cv
    #
    cmap
    co
    #
    com
    cdom
    wbr
    cA
    c0
    cmap
    co
    #
    com
    cdom
    wbr
    cA
    vy
    cv
    #
    cmap
    co
    #
    com
    cdom
    wbr
    #
    cA
    @3
    vz
    cv
    #
    csn
    #
    cun
    #
    cmap
    co
    #
    com
    cdom
    wbr
    #
    cA
    cB
    cmap
    co
    #
    com
    cdom
    wbr
    vx
    vy
    vz
    cB
    @0
    c0
    wceq
    @1
    @2
    com
    cdom
    @0
    c0
    cA
    cmap
    oveq2
    breq1d
    @0
    @3
    wceq
    @1
    @4
    com
    cdom
    @0
    @3
    cA
    cmap
    oveq2
    breq1d
    @0
    @8
    wceq
    @1
    @9
    com
    cdom
    @0
    @8
    cA
    cmap
    oveq2
    breq1d
    @0
    cB
    wceq
    @1
    @11
    com
    cdom
    @0
    cB
    cA
    cmap
    oveq2
    breq1d
    wph
    @2
    c0
    csn
    #
    com
    cdom
    wph
    cA
    cvv
    wcel
    #
    @2
    @12
    wceq
    wph
    cA
    com
    cdom
    wbr
    #
    @13
    mpct.a
    cA
    ctex
    syl
    #
    cA
    cvv
    mapdm0
    syl
    @12
    com
    cdom
    wbr
    #
    wph
    @12
    cfn
    wcel
    @16
    c0
    snfi
    @12
    fict
    ax-mp
    a1i
    eqbrtrd
    wph
    @3
    cB
    wss
    #
    @6
    cB
    @3
    cdif
    wcel
    #
    wa
    #
    wa
    #
    @5
    @10
    @20
    @5
    wa
    #
    @9
    @4
    cA
    @7
    cmap
    co
    #
    cxp
    #
    cen
    wbr
    #
    @23
    com
    cdom
    wbr
    #
    @10
    @21
    @3
    cvv
    wcel
    #
    @7
    cvv
    wcel
    #
    @13
    @3
    @7
    cin
    c0
    wceq
    #
    @24
    @26
    @21
    vy
    vex
    a1i
    @27
    @21
    @6
    snex
    a1i
    wph
    @13
    @19
    @5
    @15
    ad2antrr
    @19
    @28
    wph
    @5
    @18
    @28
    @17
    @18
    @6
    @3
    wcel
    wn
    @28
    @6
    cB
    @3
    eldifn
    @3
    @6
    disjsn
    sylibr
    adantl
    ad2antlr
    @3
    @7
    cA
    cvv
    cvv
    cvv
    mapunen
    syl31anc
    @21
    @5
    @22
    com
    cdom
    wbr
    #
    @25
    @20
    @5
    simpr
    wph
    @29
    @19
    @5
    wph
    @22
    cA
    cen
    wbr
    @14
    @29
    wph
    cA
    @6
    cvv
    cvv
    @15
    @6
    cvv
    wcel
    wph
    vz
    vex
    a1i
    mapsnend
    mpct.a
    @22
    cA
    com
    endomtr
    syl2anc
    ad2antrr
    @4
    @22
    xpct
    syl2anc
    @9
    @23
    com
    endomtr
    syl2anc
    ex
    mpct.b
    findcard2d
end
