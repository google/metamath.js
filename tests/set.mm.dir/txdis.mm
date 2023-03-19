include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "ctx.mm"
include "co.mm"
include "cxp.mm"
include "cuni.mm"
include "wss.mm"
include "wceq.mm"
include "ctop.mm"
include "distop.mm"
include "unipw.mm"
include "eqcomi.mm"
include "txuni.mm"
include "syl2an.mm"
include "eqimss2.mm"
include "syl.mm"
include "sspwuni.mm"
include "sylibr.mm"
include "cv.mm"
include "wrex.mm"
include "wral.mm"
include "c1st.mm"
include "cfv.mm"
include "csn.mm"
include "c2nd.mm"
include "cop.mm"
include "elelpwi.mm"
include "adantl.mm"
include "xp1st.mm"
include "snelpwi.mm"
include "3syl.mm"
include "xp2nd.mm"
include "vsnid.mm"
include "1st2nd2.mm"
include "sneqd.mm"
include "syl5eleq.mm"
include "simprl.mm"
include "eqeltrrd.mm"
include "snssd.mm"
include "xpeq1.mm"
include "eleq2d.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "xpeq2.mm"
include "fvex.mm"
include "xpsn.mm"
include "syl6eq.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "expr.mm"
include "ralrimdva.mm"
include "wb.mm"
include "eltx.mm"
include "sylibrd.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem txdis
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. V /\ B e. W ) -> ( ~P A tX ~P B ) = ~P ( A X. B ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cA
    cpw
    #
    cB
    cpw
    #
    ctx
    co
    #
    cA
    cB
    cxp
    #
    cpw
    #
    @2
    @5
    cuni
    #
    @6
    wss
    #
    @5
    @7
    wss
    @2
    @6
    @8
    wceq
    #
    @9
    @0
    @3
    ctop
    wcel
    #
    @4
    ctop
    wcel
    #
    @10
    @1
    cA
    cV
    distop
    #
    cB
    cW
    distop
    #
    @3
    @4
    cA
    cB
    @3
    cuni
    cA
    cA
    unipw
    eqcomi
    @4
    cuni
    cB
    cB
    unipw
    eqcomi
    txuni
    syl2an
    @8
    @6
    eqimss2
    syl
    @5
    @6
    sspwuni
    sylibr
    @2
    vx
    @7
    @5
    @2
    vx
    cv
    #
    @7
    wcel
    #
    vy
    cv
    #
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
    @20
    @15
    wss
    #
    wa
    #
    vw
    @4
    wrex
    vz
    @3
    wrex
    #
    vy
    @15
    wral
    #
    @15
    @5
    wcel
    #
    @2
    @16
    @24
    vy
    @15
    @2
    @17
    @15
    wcel
    #
    @16
    @24
    @2
    @27
    @16
    wa
    #
    wa
    #
    @17
    c1st
    cfv
    #
    csn
    #
    @3
    wcel
    #
    @17
    c2nd
    cfv
    #
    csn
    #
    @4
    wcel
    #
    @17
    @30
    @33
    cop
    #
    csn
    #
    wcel
    #
    @37
    @15
    wss
    #
    @24
    @29
    @17
    @6
    wcel
    #
    @30
    cA
    wcel
    @32
    @28
    @40
    @2
    @17
    @15
    @6
    elelpwi
    adantl
    #
    @17
    cA
    cB
    xp1st
    @30
    cA
    snelpwi
    3syl
    @29
    @40
    @33
    cB
    wcel
    @35
    @41
    @17
    cA
    cB
    xp2nd
    @33
    cB
    snelpwi
    3syl
    @29
    @17
    @17
    csn
    @37
    vy
    vsnid
    @29
    @17
    @36
    @29
    @40
    @17
    @36
    wceq
    @41
    @17
    cA
    cB
    1st2nd2
    syl
    #
    sneqd
    syl5eleq
    @29
    @36
    @15
    @29
    @17
    @36
    @15
    @42
    @2
    @27
    @16
    simprl
    eqeltrrd
    snssd
    @23
    @38
    @39
    wa
    @17
    @31
    @19
    cxp
    #
    wcel
    #
    @43
    @15
    wss
    #
    wa
    vz
    vw
    @31
    @34
    @3
    @4
    @18
    @31
    wceq
    #
    @21
    @44
    @22
    @45
    @46
    @20
    @43
    @17
    @18
    @31
    @19
    xpeq1
    #
    eleq2d
    @46
    @20
    @43
    @15
    @47
    sseq1d
    anbi12d
    @19
    @34
    wceq
    #
    @44
    @38
    @45
    @39
    @48
    @43
    @37
    @17
    @48
    @43
    @31
    @34
    cxp
    @37
    @19
    @34
    @31
    xpeq2
    @30
    @33
    @17
    c1st
    fvex
    @17
    c2nd
    fvex
    xpsn
    syl6eq
    #
    eleq2d
    @48
    @43
    @37
    @15
    @49
    sseq1d
    anbi12d
    rspc2ev
    syl112anc
    expr
    ralrimdva
    @0
    @11
    @12
    @26
    @25
    wb
    @1
    @13
    @14
    vz
    vw
    @15
    @3
    @4
    ctop
    ctop
    vy
    eltx
    syl2an
    sylibrd
    ssrdv
    eqssd
end
