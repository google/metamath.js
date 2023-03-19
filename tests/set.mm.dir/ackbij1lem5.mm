include "cv.mm"
include "csuc.mm"
include "cpw.mm"
include "ccrd.mm"
include "cfv.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "com.mm"
include "suceq.mm"
include "pweqd.mm"
include "fveq2d.mm"
include "pweq.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "wcel.mm"
include "ccda.mm"
include "cen.mm"
include "wbr.mm"
include "c2o.mm"
include "cxp.mm"
include "cmap.mm"
include "vex.mm"
include "sucex.mm"
include "pw2en.mm"
include "csn.mm"
include "cun.mm"
include "df-suc.mm"
include "oveq2i.mm"
include "word.mm"
include "cin.mm"
include "c0.mm"
include "nnord.mm"
include "orddisj.mm"
include "cvv.mm"
include "wi.mm"
include "snex.mm"
include "2onn.mm"
include "elexi.mm"
include "w3a.mm"
include "mapunen.mm"
include "ex.mm"
include "mp3an.mm"
include "3syl.mm"
include "ovex.mm"
include "enref.mm"
include "mapsnen.mm"
include "xpen.mm"
include "mp2an.mm"
include "entr.mm"
include "sylancl.mm"
include "syl5eqbr.mm"
include "ensymi.mm"
include "sylancr.mm"
include "vpwex.mm"
include "xp2cda.mm"
include "ax-mp.mm"
include "syl6breq.mm"
include "cfn.mm"
include "nnfi.mm"
include "pwfi.mm"
include "sylib.mm"
include "ficardid.mm"
include "syl.mm"
include "cdaen.mm"
include "syl2anc.mm"
include "ensymd.mm"
include "carden2b.mm"
include "ficardom.mm"
include "nnacda.mm"
include "eqtrd.mm"
include "vtoclga.mm"

theorem ackbij1lem5
  let cA: class A
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cH: class H
  let cB: class B


  assert |- ( A e. _om -> ( card ` ~P suc A ) = ( ( card ` ~P A ) +o ( card ` ~P A ) ) )

  proof
    va
    cv
    #
    csuc
    #
    cpw
    #
    ccrd
    cfv
    #
    @0
    cpw
    #
    ccrd
    cfv
    #
    @5
    coa
    co
    #
    wceq
    cA
    csuc
    #
    cpw
    #
    ccrd
    cfv
    #
    cA
    cpw
    #
    ccrd
    cfv
    #
    @11
    coa
    co
    #
    wceq
    va
    cA
    com
    @0
    cA
    wceq
    #
    @3
    @9
    @6
    @12
    @13
    @2
    @8
    ccrd
    @13
    @1
    @7
    @0
    cA
    suceq
    pweqd
    fveq2d
    @13
    @5
    @11
    @5
    @11
    coa
    @13
    @4
    @10
    ccrd
    @0
    cA
    pweq
    fveq2d
    #
    @14
    oveq12d
    eqeq12d
    @0
    com
    wcel
    #
    @3
    @5
    @5
    ccda
    co
    #
    ccrd
    cfv
    #
    @6
    @15
    @2
    @16
    cen
    wbr
    #
    @3
    @17
    wceq
    @15
    @2
    @4
    @4
    ccda
    co
    #
    cen
    wbr
    @19
    @16
    cen
    wbr
    @18
    @15
    @2
    @4
    c2o
    cxp
    #
    @19
    cen
    @15
    @2
    c2o
    @1
    cmap
    co
    #
    cen
    wbr
    @21
    @20
    cen
    wbr
    #
    @2
    @20
    cen
    wbr
    @1
    @0
    va
    vex
    #
    sucex
    pw2en
    @15
    @21
    c2o
    @0
    cmap
    co
    #
    c2o
    cxp
    #
    cen
    wbr
    @25
    @20
    cen
    wbr
    @22
    @15
    @21
    c2o
    @0
    @0
    csn
    #
    cun
    #
    cmap
    co
    #
    @25
    cen
    @1
    @27
    c2o
    cmap
    @0
    df-suc
    oveq2i
    @15
    @28
    @24
    c2o
    @26
    cmap
    co
    #
    cxp
    #
    cen
    wbr
    #
    @30
    @25
    cen
    wbr
    #
    @28
    @25
    cen
    wbr
    @15
    @0
    word
    @0
    @26
    cin
    c0
    wceq
    #
    @31
    @0
    nnord
    @0
    orddisj
    @0
    cvv
    wcel
    #
    @26
    cvv
    wcel
    #
    c2o
    cvv
    wcel
    #
    @33
    @31
    wi
    @23
    @0
    snex
    c2o
    com
    2onn
    elexi
    #
    @34
    @35
    @36
    w3a
    @33
    @31
    @0
    @26
    c2o
    cvv
    cvv
    cvv
    mapunen
    ex
    mp3an
    3syl
    @24
    @24
    cen
    wbr
    @29
    c2o
    cen
    wbr
    @32
    @24
    c2o
    @0
    cmap
    ovex
    enref
    c2o
    @0
    @37
    @23
    mapsnen
    @24
    @24
    @29
    c2o
    xpen
    mp2an
    @28
    @30
    @25
    entr
    sylancl
    syl5eqbr
    @20
    @25
    @4
    @24
    cen
    wbr
    c2o
    c2o
    cen
    wbr
    @20
    @25
    cen
    wbr
    @0
    @23
    pw2en
    c2o
    @37
    enref
    @4
    @24
    c2o
    c2o
    xpen
    mp2an
    ensymi
    @21
    @25
    @20
    entr
    sylancl
    @2
    @21
    @20
    entr
    sylancr
    @4
    cvv
    wcel
    @20
    @19
    wceq
    va
    vpwex
    @4
    cvv
    xp2cda
    ax-mp
    syl6breq
    @15
    @16
    @19
    @15
    @5
    @4
    cen
    wbr
    #
    @38
    @16
    @19
    cen
    wbr
    @15
    @4
    cfn
    wcel
    #
    @38
    @15
    @0
    cfn
    wcel
    @39
    @0
    nnfi
    @0
    pwfi
    sylib
    #
    @4
    ficardid
    syl
    #
    @41
    @5
    @4
    @5
    @4
    cdaen
    syl2anc
    ensymd
    @2
    @19
    @16
    entr
    syl2anc
    @2
    @16
    carden2b
    syl
    @15
    @5
    com
    wcel
    #
    @42
    @17
    @6
    wceq
    @15
    @39
    @42
    @40
    @4
    ficardom
    syl
    #
    @43
    @5
    @5
    nnacda
    syl2anc
    eqtrd
    vtoclga
end
