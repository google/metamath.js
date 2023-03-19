include "cinito.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "weu.mm"
include "wral.mm"
include "ccid.mm"
include "csn.mm"
include "wceq.mm"
include "isinitoi.mm"
include "wi.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "eubidv.mm"
include "rspcv.mm"
include "adantl.mm"
include "wex.mm"
include "eusn.mm"
include "eqid.mm"
include "ccat.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "catidcl.mm"
include "fvex.mm"
include "elsn.mm"
include "eqcom.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "sneqbg.mm"
include "bicomd.mm"
include "ax-mp.mm"
include "3bitri.mm"
include "biimpi.mm"
include "a1i.mm"
include "eleq2.mm"
include "eqeq1.mm"
include "3imtr4d.mm"
include "syl5.mm"
include "exlimiv.mm"
include "com12.mm"
include "syl5bi.mm"
include "syld.mm"
include "expimpd.mm"
include "mpd.mm"

theorem initoid
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cH: class H
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vh: setvar h
  let vo: setvar o
  assume isinitoi.b: |- B = ( Base ` C )
  assume isinitoi.h: |- H = ( Hom ` C )
  assume isinitoi.c: |- ( ph -> C e. Cat )


  assert |- ( ( ph /\ O e. ( InitO ` C ) ) -> ( O H O ) = { ( ( Id ` C ) ` O ) } )

  proof
    wph
    cO
    cC
    cinito
    cfv
    wcel
    #
    wa
    #
    cO
    cB
    wcel
    #
    vh
    cv
    #
    cO
    vo
    cv
    #
    cH
    co
    #
    wcel
    #
    vh
    weu
    #
    vo
    cB
    wral
    #
    wa
    cO
    cO
    cH
    co
    #
    cO
    cC
    ccid
    cfv
    #
    cfv
    #
    csn
    #
    wceq
    #
    wph
    cB
    cC
    vh
    cH
    cO
    vo
    isinitoi.b
    isinitoi.h
    isinitoi.c
    isinitoi
    @1
    @2
    @8
    @13
    @1
    @2
    wa
    #
    @8
    @3
    @9
    wcel
    #
    vh
    weu
    #
    @13
    @2
    @8
    @16
    wi
    @1
    @7
    @16
    vo
    cO
    cB
    @4
    cO
    wceq
    #
    @6
    @15
    vh
    @17
    @5
    @9
    @3
    @4
    cO
    cO
    cH
    oveq2
    eleq2d
    eubidv
    rspcv
    adantl
    @16
    @9
    @3
    csn
    #
    wceq
    #
    vh
    wex
    #
    @14
    @13
    vh
    @9
    eusn
    @20
    @14
    @13
    @19
    @14
    @13
    wi
    vh
    @14
    @11
    @9
    wcel
    #
    @19
    @13
    @14
    cB
    cC
    @10
    cH
    cO
    isinitoi.b
    isinitoi.h
    @10
    eqid
    wph
    cC
    ccat
    wcel
    @0
    @2
    isinitoi.c
    ad2antrr
    @1
    @2
    simpr
    catidcl
    @19
    @11
    @18
    wcel
    #
    @18
    @12
    wceq
    #
    @21
    @13
    @22
    @23
    wi
    @19
    @22
    @23
    @22
    @11
    @3
    wceq
    @3
    @11
    wceq
    #
    @23
    @11
    @3
    cO
    @10
    fvex
    elsn
    @11
    @3
    eqcom
    @3
    cvv
    wcel
    #
    @24
    @23
    wb
    vh
    vex
    @25
    @23
    @24
    @3
    @11
    cvv
    sneqbg
    bicomd
    ax-mp
    3bitri
    biimpi
    a1i
    @9
    @18
    @11
    eleq2
    @9
    @18
    @12
    eqeq1
    3imtr4d
    syl5
    exlimiv
    com12
    syl5bi
    syld
    expimpd
    mpd
end
