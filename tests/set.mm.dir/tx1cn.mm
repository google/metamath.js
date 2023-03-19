include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "cxp.mm"
include "cres.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "f1stres.mm"
include "a1i.mm"
include "wss.mm"
include "toponss.mm"
include "adantlr.mm"
include "xpss1.mm"
include "syl.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "fvres.mm"
include "eleq1d.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "1st2nd2.mm"
include "xp2nd.mm"
include "elxp6.mm"
include "anass.mm"
include "an32.mm"
include "3bitr2i.mm"
include "baib.mm"
include "syl2anc.mm"
include "bitr4d.mm"
include "pm5.32i.mm"
include "bitri.mm"
include "syl6rbbr.mm"
include "eqrdv.mm"
include "toponmax.mm"
include "ad2antlr.mm"
include "txopn.mm"
include "anassrs.mm"
include "mpdan.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "txtopon.mm"
include "simpl.mm"
include "iscn.mm"
include "mpbir2and.mm"

theorem tx1cn
  let cR: class R
  let cS: class S
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vz: setvar z


  assert |- ( ( R e. ( TopOn ` X ) /\ S e. ( TopOn ` Y ) ) -> ( 1st |` ( X X. Y ) ) e. ( ( R tX S ) Cn R ) )

  proof
    cR
    cX
    ctopon
    cfv
    #
    wcel
    #
    cS
    cY
    ctopon
    cfv
    #
    wcel
    #
    wa
    #
    c1st
    cX
    cY
    cxp
    #
    cres
    #
    cR
    cS
    ctx
    co
    #
    cR
    ccn
    co
    wcel
    #
    @5
    cX
    @6
    wf
    #
    @6
    ccnv
    vw
    cv
    #
    cima
    #
    @7
    wcel
    #
    vw
    cR
    wral
    #
    @9
    @4
    cX
    cY
    f1stres
    #
    a1i
    @4
    @12
    vw
    cR
    @4
    @10
    cR
    wcel
    #
    wa
    #
    @11
    @10
    cY
    cxp
    #
    @7
    @16
    vz
    @11
    @17
    @16
    vz
    cv
    #
    @17
    wcel
    #
    @18
    @5
    wcel
    #
    @19
    wa
    #
    @18
    @11
    wcel
    #
    @16
    @19
    @20
    @16
    @17
    @5
    @18
    @16
    @10
    cX
    wss
    #
    @17
    @5
    wss
    @1
    @15
    @23
    @3
    @10
    cR
    cX
    toponss
    adantlr
    @10
    cX
    cY
    xpss1
    syl
    sseld
    pm4.71rd
    @22
    @20
    @18
    @6
    cfv
    #
    @10
    wcel
    #
    wa
    #
    @21
    @9
    @6
    @5
    wfn
    @22
    @26
    wb
    @14
    @5
    cX
    @6
    ffn
    @5
    @18
    @10
    @6
    elpreima
    mp2b
    @20
    @25
    @19
    @20
    @25
    @18
    c1st
    cfv
    #
    @10
    wcel
    #
    @19
    @20
    @24
    @27
    @10
    @18
    @5
    c1st
    fvres
    eleq1d
    @20
    @18
    @27
    @18
    c2nd
    cfv
    #
    cop
    wceq
    #
    @29
    cY
    wcel
    #
    @19
    @28
    wb
    @18
    cX
    cY
    1st2nd2
    @18
    cX
    cY
    xp2nd
    @19
    @30
    @31
    wa
    #
    @28
    @19
    @30
    @28
    @31
    wa
    wa
    @30
    @28
    wa
    @31
    wa
    @32
    @28
    wa
    @18
    @10
    cY
    elxp6
    @30
    @28
    @31
    anass
    @30
    @28
    @31
    an32
    3bitr2i
    baib
    syl2anc
    bitr4d
    pm5.32i
    bitri
    syl6rbbr
    eqrdv
    @16
    cY
    cS
    wcel
    #
    @17
    @7
    wcel
    #
    @3
    @33
    @1
    @15
    cY
    cS
    toponmax
    ad2antlr
    @4
    @15
    @33
    @34
    @10
    cY
    cR
    cS
    @0
    @2
    txopn
    anassrs
    mpdan
    eqeltrd
    ralrimiva
    @4
    @7
    @5
    ctopon
    cfv
    wcel
    @1
    @8
    @9
    @13
    wa
    wb
    cR
    cS
    cX
    cY
    txtopon
    @1
    @3
    simpl
    vw
    @6
    @7
    cR
    @5
    cX
    iscn
    syl2anc
    mpbir2and
end
