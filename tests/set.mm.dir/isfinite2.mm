include "com.mm"
include "cvv.mm"
include "wcel.mm"
include "csdm.mm"
include "wbr.mm"
include "cfn.mm"
include "relsdom.mm"
include "brrelex2i.mm"
include "cv.mm"
include "cen.mm"
include "wss.mm"
include "wa.mm"
include "wex.mm"
include "cdom.mm"
include "sdomdom.mm"
include "domeng.mm"
include "syl5ib.mm"
include "wrex.mm"
include "wral.mm"
include "wn.mm"
include "ensym.mm"
include "ad2antrl.mm"
include "simpl.mm"
include "ensdomtr.mm"
include "syl2anc.mm"
include "sdomnen.mm"
include "syl.mm"
include "wi.mm"
include "simpr.mm"
include "unbnn.mm"
include "3expia.mm"
include "syl2an.mm"
include "mtod.mm"
include "rexnal.mm"
include "csuc.mm"
include "con0.mm"
include "word.mm"
include "wb.mm"
include "omsson.mm"
include "sstr.mm"
include "mpan2.mm"
include "nnord.mm"
include "cuni.mm"
include "ssel2.mm"
include "vex.mm"
include "elon.mm"
include "sylib.mm"
include "ordtri1.mm"
include "sylan.mm"
include "an32s.mm"
include "ralbidva.mm"
include "unissb.mm"
include "ralnex.mm"
include "bicomi.mm"
include "3bitr4g.mm"
include "ordunisssuc.mm"
include "bitr3d.mm"
include "peano2b.mm"
include "ssnnfi.mm"
include "sylanb.mm"
include "ex.mm"
include "adantl.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "syl5bir.mm"
include "ad2antll.mm"
include "mpd.mm"
include "simprl.mm"
include "enfii.mm"
include "exlimdv.mm"
include "sylcom.mm"
include "mpcom.mm"

theorem isfinite2
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( A ~< _om -> A e. Fin )

  proof
    com
    cvv
    wcel
    #
    cA
    com
    csdm
    wbr
    #
    cA
    cfn
    wcel
    #
    cA
    com
    csdm
    relsdom
    brrelex2i
    #
    @0
    @1
    cA
    vy
    cv
    #
    cen
    wbr
    #
    @4
    com
    wss
    #
    wa
    #
    vy
    wex
    #
    @2
    @1
    cA
    com
    cdom
    wbr
    @0
    @8
    cA
    com
    sdomdom
    vy
    cA
    com
    cvv
    domeng
    syl5ib
    @1
    @7
    @2
    vy
    @1
    @7
    @2
    @1
    @7
    wa
    #
    @4
    cfn
    wcel
    #
    @5
    @2
    @9
    vz
    cv
    #
    vw
    cv
    #
    wcel
    #
    vw
    @4
    wrex
    #
    vz
    com
    wral
    #
    wn
    #
    @10
    @9
    @15
    @4
    com
    cen
    wbr
    #
    @9
    @4
    com
    csdm
    wbr
    #
    @17
    wn
    @9
    @4
    cA
    cen
    wbr
    #
    @1
    @18
    @5
    @19
    @1
    @6
    cA
    @4
    ensym
    ad2antrl
    @1
    @7
    simpl
    @4
    cA
    com
    ensdomtr
    syl2anc
    @4
    com
    sdomnen
    syl
    @1
    @0
    @6
    @15
    @17
    wi
    @7
    @3
    @5
    @6
    simpr
    @0
    @6
    @15
    @17
    vz
    vw
    @4
    unbnn
    3expia
    syl2an
    mtod
    @6
    @16
    @10
    wi
    @1
    @5
    @16
    @14
    wn
    #
    vz
    com
    wrex
    @6
    @10
    @14
    vz
    com
    rexnal
    @6
    @20
    @10
    vz
    com
    @6
    @11
    com
    wcel
    #
    wa
    @20
    @4
    @11
    csuc
    #
    wss
    #
    @10
    @6
    @4
    con0
    wss
    #
    @11
    word
    #
    @20
    @23
    wb
    @21
    @6
    com
    con0
    wss
    @24
    omsson
    @4
    com
    con0
    sstr
    mpan2
    @11
    nnord
    @24
    @25
    wa
    #
    @4
    cuni
    @11
    wss
    #
    @20
    @23
    @26
    @12
    @11
    wss
    #
    vw
    @4
    wral
    @13
    wn
    #
    vw
    @4
    wral
    #
    @27
    @20
    @26
    @28
    @29
    vw
    @4
    @24
    @12
    @4
    wcel
    #
    @25
    @28
    @29
    wb
    #
    @24
    @31
    wa
    #
    @12
    word
    #
    @25
    @32
    @33
    @12
    con0
    wcel
    @34
    @4
    con0
    @12
    ssel2
    @12
    vw
    vex
    elon
    sylib
    @12
    @11
    ordtri1
    sylan
    an32s
    ralbidva
    vw
    @4
    @11
    unissb
    @30
    @20
    @13
    vw
    @4
    ralnex
    bicomi
    3bitr4g
    @4
    @11
    ordunisssuc
    bitr3d
    syl2an
    @21
    @23
    @10
    wi
    @6
    @21
    @23
    @10
    @21
    @22
    com
    wcel
    @23
    @10
    @11
    peano2b
    @22
    @4
    ssnnfi
    sylanb
    ex
    adantl
    sylbid
    rexlimdva
    syl5bir
    ad2antll
    mpd
    @1
    @5
    @6
    simprl
    cA
    @4
    enfii
    syl2anc
    ex
    exlimdv
    sylcom
    mpcom
end
