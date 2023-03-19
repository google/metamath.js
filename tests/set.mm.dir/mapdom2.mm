include "cdom.mm"
include "wbr.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "cvv.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "simpr.mm"
include "oveq1d.mm"
include "wne.mm"
include "simplr.mm"
include "idd.mm"
include "jctird.mm"
include "mtod.mm"
include "neqned.mm"
include "map0b.mm"
include "syl.mm"
include "eqtrd.mm"
include "ovex.mm"
include "0dom.mm"
include "syl6eqbr.mm"
include "cv.mm"
include "cen.mm"
include "wss.mm"
include "wex.mm"
include "simpll.mm"
include "wb.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "ad2antrr.mm"
include "domeng.mm"
include "mpbid.mm"
include "enrefg.mm"
include "ad2antlr.mm"
include "simprrl.mm"
include "mapen.mm"
include "syl2anc.mm"
include "cdif.mm"
include "cxp.mm"
include "ovexd.mm"
include "simprl.mm"
include "wi.mm"
include "difexg.mm"
include "map0g.mm"
include "simpl.mm"
include "syl6bi.mm"
include "necon3d.mm"
include "mpd.mm"
include "xpdom3.mm"
include "syl3anc.mm"
include "cun.mm"
include "cin.mm"
include "vex.mm"
include "a1i.mm"
include "disjdif.mm"
include "mapunen.mm"
include "syl31anc.mm"
include "ensymd.mm"
include "simprrr.mm"
include "undif.mm"
include "sylib.mm"
include "oveq2d.mm"
include "breqtrd.mm"
include "domentr.mm"
include "endomtr.mm"
include "expr.mm"
include "exlimdv.mm"
include "adantlr.mm"
include "pm2.61dane.mm"
include "an32s.mm"
include "ex.mm"
include "reldmmap.mm"
include "ovprc1.mm"
include "pm2.61d1.mm"

theorem mapdom2
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let cV: class V
  let cW: class W


  assert |- ( ( A ~<_ B /\ -. ( A = (/) /\ C = (/) ) ) -> ( C ^m A ) ~<_ ( C ^m B ) )

  proof
    cA
    cB
    cdom
    wbr
    #
    cA
    c0
    wceq
    #
    cC
    c0
    wceq
    #
    wa
    #
    wn
    #
    wa
    #
    cC
    cvv
    wcel
    #
    cC
    cA
    cmap
    co
    #
    cC
    cB
    cmap
    co
    #
    cdom
    wbr
    #
    @5
    @6
    @9
    @0
    @6
    @4
    @9
    @0
    @6
    wa
    #
    @4
    wa
    #
    @9
    cC
    c0
    @11
    @2
    wa
    #
    @7
    c0
    @8
    cdom
    @12
    @7
    c0
    cA
    cmap
    co
    #
    c0
    @12
    cC
    c0
    cA
    cmap
    @11
    @2
    simpr
    #
    oveq1d
    @12
    cA
    c0
    wne
    @13
    c0
    wceq
    @12
    cA
    c0
    @12
    @1
    @3
    @10
    @4
    @2
    simplr
    @12
    @1
    @1
    @2
    @12
    @1
    idd
    @14
    jctird
    mtod
    neqned
    cA
    map0b
    syl
    eqtrd
    @8
    cC
    cB
    cmap
    ovex
    0dom
    #
    syl6eqbr
    @10
    cC
    c0
    wne
    #
    @9
    @4
    @10
    @16
    wa
    #
    cA
    vx
    cv
    #
    cen
    wbr
    #
    @18
    cB
    wss
    #
    wa
    #
    vx
    wex
    #
    @9
    @17
    @0
    @22
    @0
    @6
    @16
    simpll
    @17
    cB
    cvv
    wcel
    #
    @0
    @22
    wb
    @0
    @23
    @6
    @16
    cA
    cB
    cdom
    reldom
    brrelex2i
    #
    ad2antrr
    vx
    cA
    cB
    cvv
    domeng
    syl
    mpbid
    @17
    @21
    @9
    vx
    @10
    @16
    @21
    @9
    @10
    @16
    @21
    wa
    #
    wa
    #
    @7
    cC
    @18
    cmap
    co
    #
    cen
    wbr
    #
    @27
    @8
    cdom
    wbr
    #
    @9
    @26
    cC
    cC
    cen
    wbr
    #
    @19
    @28
    @6
    @30
    @0
    @25
    cC
    cvv
    enrefg
    ad2antlr
    @10
    @16
    @19
    @20
    simprrl
    cC
    cC
    cA
    @18
    mapen
    syl2anc
    @26
    @27
    @27
    cC
    cB
    @18
    cdif
    #
    cmap
    co
    #
    cxp
    #
    cdom
    wbr
    #
    @33
    @8
    cen
    wbr
    @29
    @26
    @27
    cvv
    wcel
    @32
    cvv
    wcel
    @32
    c0
    wne
    #
    @34
    @26
    cC
    @18
    cmap
    ovexd
    @26
    cC
    @31
    cmap
    ovexd
    @26
    @16
    @35
    @10
    @16
    @21
    simprl
    @26
    @6
    @31
    cvv
    wcel
    #
    @16
    @35
    wi
    @0
    @6
    @25
    simplr
    #
    @26
    @23
    @36
    @0
    @23
    @6
    @25
    @24
    ad2antrr
    cB
    @18
    cvv
    difexg
    syl
    #
    @6
    @36
    wa
    #
    @32
    c0
    cC
    c0
    @39
    @32
    c0
    wceq
    @2
    @31
    c0
    wne
    #
    wa
    @2
    cC
    @31
    cvv
    cvv
    map0g
    @2
    @40
    simpl
    syl6bi
    necon3d
    syl2anc
    mpd
    @27
    @32
    cvv
    cvv
    xpdom3
    syl3anc
    @26
    @33
    cC
    @18
    @31
    cun
    #
    cmap
    co
    #
    @8
    cen
    @26
    @42
    @33
    @26
    @18
    cvv
    wcel
    #
    @36
    @6
    @18
    @31
    cin
    c0
    wceq
    #
    @42
    @33
    cen
    wbr
    @43
    @26
    vx
    vex
    a1i
    @38
    @37
    @44
    @26
    @18
    cB
    disjdif
    a1i
    @18
    @31
    cC
    cvv
    cvv
    cvv
    mapunen
    syl31anc
    ensymd
    @26
    @41
    cB
    cC
    cmap
    @26
    @20
    @41
    cB
    wceq
    @10
    @16
    @19
    @20
    simprrr
    @18
    cB
    undif
    sylib
    oveq2d
    breqtrd
    @27
    @33
    @8
    domentr
    syl2anc
    @7
    @27
    @8
    endomtr
    syl2anc
    expr
    exlimdv
    mpd
    adantlr
    pm2.61dane
    an32s
    ex
    @6
    wn
    @7
    c0
    @8
    cdom
    cC
    cA
    cmap
    reldmmap
    ovprc1
    @15
    syl6eqbr
    pm2.61d1
end
