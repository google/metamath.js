include "c0.mm"
include "cpr.mm"
include "ctx.mm"
include "co.mm"
include "cid.mm"
include "cfv.mm"
include "cxp.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wex.mm"
include "neq0.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "wi.mm"
include "ctop.mm"
include "wb.mm"
include "indistop.mm"
include "eltx.mm"
include "mp2an.mm"
include "rsp.mm"
include "sylbi.mm"
include "cuni.mm"
include "elssuni.mm"
include "indisuni.mm"
include "txunii.mm"
include "syl6sseqr.mm"
include "ad2antrr.mm"
include "wne.mm"
include "ne0i.mm"
include "ad2antrl.mm"
include "xpnz.mm"
include "sylibr.mm"
include "simpld.mm"
include "neneqd.mm"
include "simpll.mm"
include "indislem.mm"
include "syl6eleqr.mm"
include "elpri.mm"
include "syl.mm"
include "ord.mm"
include "mpd.mm"
include "simprd.mm"
include "simplr.mm"
include "xpeq12d.mm"
include "simprr.mm"
include "eqsstr3d.mm"
include "adantll.mm"
include "eqssd.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "syld.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "orrd.mm"
include "vex.mm"
include "elpr.mm"
include "ssriv.mm"
include "cpw.mm"
include "ctopon.mm"
include "toptopon.mm"
include "mpbi.mm"
include "txtopon.mm"
include "topgele.mm"
include "ax-mp.mm"
include "simpli.mm"
include "eqssi.mm"
include "txindislem.mm"
include "preq2i.mm"
include "3eqtri.mm"

theorem txindis
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cV: class V
  let cW: class W


  assert |- ( { (/) , A } tX { (/) , B } ) = { (/) , ( A X. B ) }

  proof
    c0
    cA
    cpr
    #
    c0
    cB
    cpr
    #
    ctx
    co
    #
    c0
    cA
    cid
    cfv
    #
    cB
    cid
    cfv
    #
    cxp
    #
    cpr
    #
    c0
    cA
    cB
    cxp
    #
    cid
    cfv
    #
    cpr
    c0
    @7
    cpr
    @2
    @6
    vx
    @2
    @6
    vx
    cv
    #
    @2
    wcel
    #
    @9
    c0
    wceq
    #
    @9
    @5
    wceq
    #
    wo
    @9
    @6
    wcel
    @10
    @11
    @12
    @11
    wn
    vy
    cv
    #
    @9
    wcel
    #
    vy
    wex
    @10
    @12
    vy
    @9
    neq0
    @10
    @14
    @12
    vy
    @10
    @14
    @13
    vz
    cv
    #
    vw
    cv
    #
    cxp
    #
    wcel
    #
    @17
    @9
    wss
    #
    wa
    #
    vw
    @1
    wrex
    vz
    @0
    wrex
    #
    @12
    @10
    @21
    vy
    @9
    wral
    #
    @14
    @21
    wi
    @0
    ctop
    wcel
    #
    @1
    ctop
    wcel
    #
    @10
    @22
    wb
    cA
    indistop
    #
    cB
    indistop
    #
    vz
    vw
    @9
    @0
    @1
    ctop
    ctop
    vy
    eltx
    mp2an
    @21
    vy
    @9
    rsp
    sylbi
    @10
    @20
    @12
    vz
    vw
    @0
    @1
    @10
    @15
    @0
    wcel
    #
    @16
    @1
    wcel
    #
    wa
    #
    wa
    #
    @20
    @12
    @30
    @20
    wa
    @9
    @5
    @10
    @9
    @5
    wss
    @29
    @20
    @10
    @9
    @2
    cuni
    @5
    @9
    @2
    elssuni
    @0
    @1
    @3
    @4
    @25
    @26
    cA
    indisuni
    #
    cB
    indisuni
    #
    txunii
    syl6sseqr
    ad2antrr
    @29
    @20
    @5
    @9
    wss
    @10
    @29
    @20
    wa
    #
    @5
    @17
    @9
    @33
    @15
    @3
    @16
    @4
    @33
    @15
    c0
    wceq
    #
    wn
    @15
    @3
    wceq
    #
    @33
    @15
    c0
    @33
    @15
    c0
    wne
    #
    @16
    c0
    wne
    #
    @33
    @17
    c0
    wne
    #
    @36
    @37
    wa
    @18
    @38
    @29
    @19
    @17
    @13
    ne0i
    ad2antrl
    @15
    @16
    xpnz
    sylibr
    #
    simpld
    neneqd
    @33
    @34
    @35
    @33
    @15
    c0
    @3
    cpr
    #
    wcel
    @34
    @35
    wo
    @33
    @15
    @0
    @40
    @27
    @28
    @20
    simpll
    cA
    indislem
    syl6eleqr
    @15
    c0
    @3
    elpri
    syl
    ord
    mpd
    @33
    @16
    c0
    wceq
    #
    wn
    @16
    @4
    wceq
    #
    @33
    @16
    c0
    @33
    @36
    @37
    @39
    simprd
    neneqd
    @33
    @41
    @42
    @33
    @16
    c0
    @4
    cpr
    #
    wcel
    @41
    @42
    wo
    @33
    @16
    @1
    @43
    @27
    @28
    @20
    simplr
    cB
    indislem
    syl6eleqr
    @16
    c0
    @4
    elpri
    syl
    ord
    mpd
    xpeq12d
    @29
    @18
    @19
    simprr
    eqsstr3d
    adantll
    eqssd
    ex
    rexlimdvva
    syld
    exlimdv
    syl5bi
    orrd
    @9
    c0
    @5
    vx
    vex
    elpr
    sylibr
    ssriv
    @6
    @2
    wss
    #
    @2
    @5
    cpw
    wss
    #
    @2
    @5
    ctopon
    cfv
    wcel
    #
    @44
    @45
    wa
    @0
    @3
    ctopon
    cfv
    wcel
    #
    @1
    @4
    ctopon
    cfv
    wcel
    #
    @46
    @23
    @47
    @25
    @0
    @3
    @31
    toptopon
    mpbi
    @24
    @48
    @26
    @1
    @4
    @32
    toptopon
    mpbi
    @0
    @1
    @3
    @4
    txtopon
    mp2an
    @2
    @5
    topgele
    ax-mp
    simpli
    eqssi
    @5
    @8
    c0
    cA
    cB
    txindislem
    preq2i
    @7
    indislem
    3eqtri
end
