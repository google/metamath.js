include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "cdif.mm"
include "csdm.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "cufil.mm"
include "cfv.mm"
include "wrex.mm"
include "cen.mm"
include "wral.mm"
include "cfil.mm"
include "wcel.mm"
include "ccrd.mm"
include "cdm.mm"
include "cvv.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "numth3.mm"
include "syl.mm"
include "csdfil.mm"
include "mpancom.mm"
include "filssufil.mm"
include "wa.mm"
include "wn.mm"
include "elfvex.mm"
include "ad2antlr.mm"
include "ufilfil.mm"
include "filelss.mm"
include "sylan.mm"
include "adantll.mm"
include "ssdomg.mm"
include "sylc.mm"
include "wi.mm"
include "cfbas.mm"
include "filfbas.mm"
include "adantl.mm"
include "fbncp.mm"
include "w3a.mm"
include "difss.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "3ad2ant1.mm"
include "wceq.mm"
include "simp2.mm"
include "dfss4.mm"
include "sylib.mm"
include "simp3.mm"
include "eqbrtrd.mm"
include "difeq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ssel.mm"
include "syl5com.mm"
include "3expa.mm"
include "impancom.mm"
include "con3d.mm"
include "syl21anc.mm"
include "bren2.mm"
include "simplbi2.mm"
include "sylsyld.mm"
include "ralrimdva.mm"
include "reximdva.mm"
include "mpd.mm"

theorem ufilen
  let vx: setvar x
  let vf: setvar f
  let cX: class X
  let vy: setvar y

  disjoint f x
  disjoint X f
  disjoint X x
  disjoint f y
  disjoint x y
  disjoint X y
  assert |- ( _om ~<_ X -> E. f e. ( UFil ` X ) A. x e. f x ~~ X )

  proof
    com
    cX
    cdom
    wbr
    #
    cX
    vy
    cv
    #
    cdif
    #
    cX
    csdm
    wbr
    #
    vy
    cX
    cpw
    #
    crab
    #
    vf
    cv
    #
    wss
    #
    vf
    cX
    cufil
    cfv
    #
    wrex
    #
    vx
    cv
    #
    cX
    cen
    wbr
    #
    vx
    @6
    wral
    #
    vf
    @8
    wrex
    @0
    @5
    cX
    cfil
    cfv
    #
    wcel
    #
    @9
    cX
    ccrd
    cdm
    wcel
    #
    @0
    @14
    @0
    cX
    cvv
    wcel
    #
    @15
    com
    cX
    cdom
    reldom
    brrelex2i
    cX
    cvv
    numth3
    syl
    vy
    cX
    csdfil
    mpancom
    vf
    @5
    cX
    filssufil
    syl
    @0
    @7
    @12
    vf
    @8
    @0
    @6
    @8
    wcel
    #
    wa
    #
    @7
    @11
    vx
    @6
    @18
    @10
    @6
    wcel
    #
    wa
    #
    @10
    cX
    cdom
    wbr
    #
    @7
    @10
    cX
    csdm
    wbr
    #
    wn
    #
    @11
    @20
    @16
    @10
    cX
    wss
    #
    @21
    @17
    @16
    @0
    @19
    @6
    cX
    cufil
    elfvex
    ad2antlr
    #
    @17
    @19
    @24
    @0
    @17
    @6
    @13
    wcel
    #
    @19
    @24
    @6
    cX
    ufilfil
    #
    @10
    @6
    cX
    filelss
    sylan
    adantll
    #
    @10
    cX
    cvv
    ssdomg
    sylc
    @20
    @16
    @24
    cX
    @10
    cdif
    #
    @6
    wcel
    #
    wn
    #
    @7
    @23
    wi
    @25
    @28
    @18
    @6
    cX
    cfbas
    cfv
    wcel
    #
    @19
    @31
    @17
    @32
    @0
    @17
    @26
    @32
    @27
    @6
    cX
    filfbas
    syl
    adantl
    @10
    cX
    @6
    cX
    fbncp
    sylan
    @16
    @24
    wa
    #
    @7
    @31
    @23
    @33
    @7
    wa
    @22
    @30
    @33
    @22
    @7
    @30
    @16
    @24
    @22
    @7
    @30
    wi
    @16
    @24
    @22
    w3a
    #
    @29
    @5
    wcel
    #
    @7
    @30
    @34
    @29
    @4
    wcel
    #
    cX
    @29
    cdif
    #
    cX
    csdm
    wbr
    #
    @35
    @16
    @24
    @36
    @22
    @16
    @36
    @29
    cX
    wss
    cX
    @10
    difss
    @29
    cX
    cvv
    elpw2g
    mpbiri
    3ad2ant1
    @34
    @37
    @10
    cX
    csdm
    @34
    @24
    @37
    @10
    wceq
    @16
    @24
    @22
    simp2
    @10
    cX
    dfss4
    sylib
    @16
    @24
    @22
    simp3
    eqbrtrd
    @3
    @38
    vy
    @29
    @4
    @1
    @29
    wceq
    @2
    @37
    cX
    csdm
    @1
    @29
    cX
    difeq2
    breq1d
    elrab
    sylanbrc
    @5
    @6
    @29
    ssel
    syl5com
    3expa
    impancom
    con3d
    impancom
    syl21anc
    @11
    @21
    @23
    @10
    cX
    bren2
    simplbi2
    sylsyld
    ralrimdva
    reximdva
    mpd
end
