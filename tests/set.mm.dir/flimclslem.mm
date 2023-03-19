include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "ccl.mm"
include "w3a.mm"
include "cfil.mm"
include "cflim.mm"
include "co.mm"
include "csn.mm"
include "cnei.mm"
include "cun.mm"
include "cfi.mm"
include "cfg.mm"
include "cfbas.mm"
include "cpw.mm"
include "c0.mm"
include "wne.mm"
include "wn.mm"
include "cuni.mm"
include "ctop.mm"
include "topontop.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "neisspw.mm"
include "syl.mm"
include "wceq.mm"
include "toponuni.mm"
include "pweqd.mm"
include "sseqtr4d.mm"
include "wb.mm"
include "toponmax.mm"
include "elpw2g.mm"
include "biimpar.mm"
include "3adant3.mm"
include "snssd.mm"
include "unssd.mm"
include "ssun2.mm"
include "cvv.mm"
include "simp2.mm"
include "ssexd.mm"
include "snnzg.mm"
include "ssn0.mm"
include "sylancr.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "wa.mm"
include "wi.mm"
include "sseqtrd.mm"
include "simp3.mm"
include "neindisj.mm"
include "expr.mm"
include "syl21anc.mm"
include "imp.mm"
include "elsni.mm"
include "ineq2d.mm"
include "neeq1d.mm"
include "syl5ibrcom.mm"
include "ralrimiv.mm"
include "ralrimiva.mm"
include "simp1.mm"
include "clsss3.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "eleqtrrd.mm"
include "3ad2ant3.mm"
include "neifil.mm"
include "syl3anc.mm"
include "filfbas.mm"
include "ne0i.mm"
include "cls0.mm"
include "neeqtrrd.mm"
include "fveq2.mm"
include "necon3i.mm"
include "snfbas.mm"
include "fbunfip.mm"
include "mpbird.mm"
include "fsubbas.mm"
include "mpbir3and.mm"
include "fgcl.mm"
include "syl5eqel.mm"
include "fvex.mm"
include "snex.mm"
include "unex.mm"
include "ssfii.mm"
include "ax-mp.mm"
include "ssfg.mm"
include "syl6sseqr.mm"
include "syl5ss.mm"
include "snssg.mm"
include "mpbiri.mm"
include "unssad.mm"
include "elflim.mm"
include "mpbir2and.mm"
include "3jca.mm"

theorem flimclslem
  let cA: class A
  let cS: class S
  let cF: class F
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume flimcls.2: |- F = ( X filGen ( fi ` ( ( ( nei ` J ) ` { A } ) u. { S } ) ) )


  assert |- ( ( J e. ( TopOn ` X ) /\ S C_ X /\ A e. ( ( cls ` J ) ` S ) ) -> ( F e. ( Fil ` X ) /\ S e. F /\ A e. ( J fLim F ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cS
    cX
    wss
    #
    cA
    cS
    cJ
    ccl
    cfv
    #
    cfv
    #
    wcel
    #
    w3a
    #
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    cS
    cF
    wcel
    cA
    cJ
    cF
    cflim
    co
    wcel
    #
    @5
    cF
    cX
    cA
    csn
    #
    cJ
    cnei
    cfv
    #
    cfv
    #
    cS
    csn
    #
    cun
    #
    cfi
    cfv
    #
    cfg
    co
    #
    @6
    flimcls.2
    @5
    @14
    cX
    cfbas
    cfv
    #
    wcel
    #
    @15
    @6
    wcel
    @5
    @17
    @13
    cX
    cpw
    #
    wss
    #
    @13
    c0
    wne
    #
    c0
    @14
    wcel
    wn
    #
    @5
    @11
    @12
    @18
    @5
    @11
    cJ
    cuni
    #
    cpw
    #
    @18
    @5
    cJ
    ctop
    wcel
    #
    @11
    @23
    wss
    @0
    @1
    @24
    @4
    cX
    cJ
    topontop
    3ad2ant1
    #
    @9
    cJ
    @22
    @22
    eqid
    #
    neisspw
    syl
    @5
    cX
    @22
    @0
    @1
    cX
    @22
    wceq
    @4
    cX
    cJ
    toponuni
    3ad2ant1
    #
    pweqd
    sseqtr4d
    @5
    cS
    @18
    @0
    @1
    cS
    @18
    wcel
    #
    @4
    @0
    @28
    @1
    @0
    cX
    cJ
    wcel
    #
    @28
    @1
    wb
    cX
    cJ
    toponmax
    #
    cS
    cX
    cJ
    elpw2g
    syl
    biimpar
    3adant3
    snssd
    unssd
    @5
    @12
    @13
    wss
    #
    @12
    c0
    wne
    #
    @20
    @12
    @11
    ssun2
    #
    @5
    cS
    cvv
    wcel
    #
    @32
    @5
    cS
    cX
    cJ
    @0
    @1
    @29
    @4
    @30
    3ad2ant1
    #
    @0
    @1
    @4
    simp2
    #
    ssexd
    #
    cS
    cvv
    snnzg
    syl
    @12
    @13
    ssn0
    sylancr
    @5
    @21
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    c0
    wne
    #
    vy
    @12
    wral
    #
    vx
    @11
    wral
    #
    @5
    @42
    vx
    @11
    @5
    @38
    @11
    wcel
    #
    wa
    #
    @41
    vy
    @12
    @45
    @41
    @39
    @12
    wcel
    #
    @38
    cS
    cin
    #
    c0
    wne
    #
    @5
    @44
    @48
    @5
    @24
    cS
    @22
    wss
    #
    @4
    @44
    @48
    wi
    @25
    @5
    cS
    cX
    @22
    @36
    @27
    sseqtrd
    #
    @0
    @1
    @4
    simp3
    #
    @24
    @49
    wa
    @4
    @44
    @48
    cA
    cS
    cJ
    @38
    @22
    @26
    neindisj
    expr
    syl21anc
    imp
    @46
    @40
    @47
    c0
    @46
    @39
    cS
    @38
    @39
    cS
    elsni
    ineq2d
    neeq1d
    syl5ibrcom
    ralrimiv
    ralrimiva
    @5
    @11
    @16
    wcel
    #
    @12
    @16
    wcel
    #
    @21
    @43
    wb
    @5
    @11
    @6
    wcel
    #
    @52
    @5
    @0
    @9
    cX
    wss
    @9
    c0
    wne
    #
    @54
    @0
    @1
    @4
    simp1
    #
    @5
    cA
    cX
    @5
    cA
    @22
    cX
    @5
    @3
    @22
    cA
    @5
    @24
    @49
    @3
    @22
    wss
    @25
    @50
    cS
    cJ
    @22
    @26
    clsss3
    syl2anc
    @51
    sseldd
    @27
    eleqtrrd
    #
    snssd
    @4
    @0
    @55
    @1
    cA
    @3
    snnzg
    3ad2ant3
    @9
    cJ
    cX
    neifil
    syl3anc
    @11
    cX
    filfbas
    syl
    @5
    @1
    cS
    c0
    wne
    #
    @29
    @53
    @36
    @5
    @3
    c0
    @2
    cfv
    #
    wne
    @58
    @5
    @3
    c0
    @59
    @4
    @0
    @3
    c0
    wne
    @1
    @3
    cA
    ne0i
    3ad2ant3
    @5
    @24
    @59
    c0
    wceq
    @25
    cJ
    cls0
    syl
    neeqtrrd
    cS
    c0
    @3
    @59
    cS
    c0
    @2
    fveq2
    necon3i
    syl
    @35
    cS
    cX
    cJ
    snfbas
    syl3anc
    vx
    vy
    @11
    @12
    cX
    cX
    fbunfip
    syl2anc
    mpbird
    @5
    @29
    @17
    @19
    @20
    @21
    w3a
    wb
    @35
    @13
    cJ
    cX
    fsubbas
    syl
    mpbir3and
    #
    @14
    cX
    fgcl
    syl
    syl5eqel
    #
    @5
    @13
    cF
    cS
    @5
    @13
    @14
    cF
    @13
    cvv
    wcel
    @13
    @14
    wss
    @11
    @12
    @9
    @10
    fvex
    cS
    snex
    unex
    @13
    cvv
    ssfii
    ax-mp
    @5
    @14
    @15
    cF
    @5
    @17
    @14
    @15
    wss
    @60
    @14
    cX
    ssfg
    syl
    flimcls.2
    syl6sseqr
    syl5ss
    #
    @5
    cS
    @13
    wcel
    #
    @31
    @33
    @5
    @34
    @63
    @31
    wb
    @37
    cS
    @13
    cvv
    snssg
    syl
    mpbiri
    sseldd
    @5
    @8
    cA
    cX
    wcel
    #
    @11
    cF
    wss
    #
    @57
    @5
    @11
    @12
    cF
    @62
    unssad
    @5
    @0
    @7
    @8
    @64
    @65
    wa
    wb
    @56
    @61
    cA
    cF
    cJ
    cX
    elflim
    syl2anc
    mpbir2and
    3jca
end
