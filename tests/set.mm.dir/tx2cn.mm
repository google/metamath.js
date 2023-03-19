include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "c2nd.mm"
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
include "f2ndres.mm"
include "a1i.mm"
include "wss.mm"
include "toponss.mm"
include "adantll.mm"
include "xpss2.mm"
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
include "c1st.mm"
include "cop.mm"
include "wceq.mm"
include "1st2nd2.mm"
include "xp1st.mm"
include "elxp6.mm"
include "anass.mm"
include "bitr4i.mm"
include "baib.mm"
include "syl2anc.mm"
include "bitr4d.mm"
include "pm5.32i.mm"
include "bitri.mm"
include "syl6rbbr.mm"
include "eqrdv.mm"
include "wi.mm"
include "toponmax.mm"
include "txopn.mm"
include "expr.mm"
include "mpidan.mm"
include "imp.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "txtopon.mm"
include "iscn.mm"
include "sylancom.mm"
include "mpbir2and.mm"

theorem tx2cn
  let cR: class R
  let cS: class S
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vz: setvar z


  assert |- ( ( R e. ( TopOn ` X ) /\ S e. ( TopOn ` Y ) ) -> ( 2nd |` ( X X. Y ) ) e. ( ( R tX S ) Cn S ) )

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
    c2nd
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
    cS
    ccn
    co
    wcel
    #
    @5
    cY
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
    cS
    wral
    #
    @9
    @4
    cX
    cY
    f2ndres
    #
    a1i
    @4
    @12
    vw
    cS
    @4
    @10
    cS
    wcel
    #
    wa
    #
    @11
    cX
    @10
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
    cY
    wss
    #
    @17
    @5
    wss
    @3
    @15
    @23
    @1
    @10
    cS
    cY
    toponss
    adantll
    @10
    cY
    cX
    xpss2
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
    cY
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
    c2nd
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
    c2nd
    fvres
    eleq1d
    @20
    @18
    @18
    c1st
    cfv
    #
    @27
    cop
    wceq
    #
    @29
    cX
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
    xp1st
    @19
    @30
    @31
    wa
    #
    @28
    @19
    @30
    @31
    @28
    wa
    wa
    @32
    @28
    wa
    @18
    cX
    @10
    elxp6
    @30
    @31
    @28
    anass
    bitr4i
    baib
    syl2anc
    bitr4d
    pm5.32i
    bitri
    syl6rbbr
    eqrdv
    @4
    @15
    @17
    @7
    wcel
    #
    @1
    @3
    cX
    cR
    wcel
    #
    @15
    @33
    wi
    cX
    cR
    toponmax
    @4
    @34
    @15
    @33
    cX
    @10
    cR
    cS
    @0
    @2
    txopn
    expr
    mpidan
    imp
    eqeltrd
    ralrimiva
    @1
    @3
    @7
    @5
    ctopon
    cfv
    wcel
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
    vw
    @6
    @7
    cS
    @5
    cY
    iscn
    sylancom
    mpbir2and
end
