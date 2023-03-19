include "wcel.mm"
include "ctopon.mm"
include "cfv.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "toponuni.mm"
include "eqimss2.mm"
include "sspwuni.mm"
include "sylibr.mm"
include "syl.mm"
include "selpw.mm"
include "ssriv.mm"
include "a1i.mm"
include "distopon.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cint.mm"
include "ctop.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "wral.mm"
include "wel.mm"
include "simpl.mm"
include "sselda.mm"
include "adantrl.mm"
include "topontop.mm"
include "intss1.mm"
include "adantl.mm"
include "sstrd.mm"
include "uniopn.mm"
include "syl2anc.mm"
include "expr.mm"
include "ralrimiv.mm"
include "vuniex.mm"
include "elint2.mm"
include "ex.mm"
include "alrimiv.mm"
include "simpll.mm"
include "simplrl.mm"
include "sseldd.mm"
include "simplrr.mm"
include "inopn.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "vex.mm"
include "inex1.mm"
include "ralrimivva.mm"
include "cvv.mm"
include "wb.mm"
include "intex.mm"
include "biimpi.mm"
include "istopg.mm"
include "mpbir2and.mm"
include "3adant1.mm"
include "wex.mm"
include "n0.mm"
include "ad2antlr.mm"
include "ancoms.mm"
include "elssuni.mm"
include "sseqtr4d.mm"
include "exlimdv.mm"
include "mpd.mm"
include "unissb.mm"
include "eqid.mm"
include "topopn.mm"
include "3syl.mm"
include "eqeltrd.mm"
include "elintg.mm"
include "3ad2ant1.mm"
include "mpbird.mm"
include "unissel.mm"
include "eqcomd.mm"
include "istopon.mm"
include "sylanbrc.mm"
include "ismred.mm"

theorem toponmre
  let cB: class B
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let cK: class K


  assert |- ( B e. V -> ( TopOn ` B ) e. ( Moore ` ~P B ) )

  proof
    cB
    cV
    wcel
    #
    cB
    ctopon
    cfv
    #
    cB
    cpw
    #
    vb
    @1
    @2
    cpw
    #
    wss
    @0
    vb
    @1
    @3
    vb
    cv
    #
    @1
    wcel
    #
    @4
    @2
    wss
    #
    @4
    @3
    wcel
    @5
    cB
    @4
    cuni
    #
    wceq
    #
    @6
    cB
    @4
    toponuni
    @8
    @7
    cB
    wss
    @6
    @7
    cB
    eqimss2
    @4
    cB
    sspwuni
    sylibr
    syl
    vb
    @2
    selpw
    sylibr
    ssriv
    a1i
    cB
    cV
    distopon
    @0
    @4
    @1
    wss
    #
    @4
    c0
    wne
    #
    w3a
    #
    @4
    cint
    #
    ctop
    wcel
    #
    cB
    @12
    cuni
    #
    wceq
    @12
    @1
    wcel
    @9
    @10
    @13
    @0
    @9
    @10
    wa
    #
    @13
    vc
    cv
    #
    @12
    wss
    #
    @16
    cuni
    #
    @12
    wcel
    #
    wi
    #
    vc
    wal
    #
    @16
    vx
    cv
    #
    cin
    #
    @12
    wcel
    #
    vx
    @12
    wral
    vc
    @12
    wral
    #
    @15
    @20
    vc
    @15
    @17
    @19
    @15
    @17
    wa
    #
    @18
    @22
    wcel
    #
    vx
    @4
    wral
    @19
    @26
    @27
    vx
    @4
    @15
    @17
    vx
    vb
    wel
    #
    @27
    @15
    @17
    @28
    wa
    #
    wa
    #
    @22
    ctop
    wcel
    #
    @16
    @22
    wss
    #
    @27
    @30
    @22
    @1
    wcel
    #
    @31
    @15
    @28
    @33
    @17
    @15
    @4
    @1
    @22
    @9
    @10
    simpl
    #
    sselda
    #
    adantrl
    cB
    @22
    topontop
    syl
    @29
    @32
    @15
    @29
    @16
    @12
    @22
    @17
    @28
    simpl
    @28
    @12
    @22
    wss
    @17
    @22
    @4
    intss1
    #
    adantl
    sstrd
    adantl
    @16
    @22
    uniopn
    syl2anc
    expr
    ralrimiv
    vx
    @18
    @4
    vc
    vuniex
    elint2
    sylibr
    ex
    alrimiv
    @15
    @24
    vc
    vx
    @12
    @12
    @15
    @16
    @12
    wcel
    #
    @22
    @12
    wcel
    #
    wa
    #
    wa
    #
    @23
    vy
    cv
    #
    wcel
    #
    vy
    @4
    wral
    @24
    @40
    @42
    vy
    @4
    @40
    vy
    vb
    wel
    #
    wa
    #
    @41
    ctop
    wcel
    #
    vc
    vy
    wel
    vx
    vy
    wel
    @42
    @44
    @41
    @1
    wcel
    @45
    @40
    @4
    @1
    @41
    @9
    @10
    @39
    simpll
    sselda
    cB
    @41
    topontop
    syl
    @44
    @12
    @41
    @16
    @43
    @12
    @41
    wss
    @40
    @41
    @4
    intss1
    adantl
    #
    @15
    @37
    @38
    @43
    simplrl
    sseldd
    @44
    @12
    @41
    @22
    @46
    @15
    @37
    @38
    @43
    simplrr
    sseldd
    @16
    @22
    @41
    inopn
    syl3anc
    ralrimiva
    vy
    @23
    @4
    @16
    @22
    vc
    vex
    inex1
    elint2
    sylibr
    ralrimivva
    @15
    @12
    cvv
    wcel
    #
    @13
    @21
    @25
    wa
    wb
    @10
    @47
    @9
    @10
    @47
    @4
    intex
    biimpi
    adantl
    vc
    vx
    cvv
    @12
    istopg
    syl
    mpbir2and
    3adant1
    @11
    @14
    cB
    @11
    @14
    cB
    wss
    #
    cB
    @12
    wcel
    #
    @14
    cB
    wceq
    @9
    @10
    @48
    @0
    @15
    @16
    cB
    wss
    #
    vc
    @12
    wral
    @48
    @15
    @50
    vc
    @12
    @15
    @37
    wa
    #
    @28
    vx
    wex
    #
    @50
    @10
    @52
    @9
    @37
    @10
    @52
    vx
    @4
    n0
    biimpi
    ad2antlr
    @51
    @28
    @50
    vx
    @15
    @37
    @28
    @50
    @15
    @37
    @28
    wa
    #
    wa
    #
    @16
    @22
    cuni
    #
    cB
    @53
    @16
    @55
    wss
    #
    @15
    @53
    vc
    vx
    wel
    #
    @56
    @28
    @37
    @57
    @28
    @12
    @22
    @16
    @36
    sselda
    ancoms
    @16
    @22
    elssuni
    syl
    adantl
    @54
    @33
    cB
    @55
    wceq
    @15
    @28
    @33
    @37
    @35
    adantrl
    cB
    @22
    toponuni
    syl
    sseqtr4d
    expr
    exlimdv
    mpd
    ralrimiva
    vc
    @12
    cB
    unissb
    sylibr
    3adant1
    @11
    @49
    cB
    @16
    wcel
    #
    vc
    @4
    wral
    #
    @9
    @10
    @59
    @0
    @15
    @58
    vc
    @4
    @15
    vc
    vb
    wel
    wa
    #
    cB
    @18
    @16
    @60
    @16
    @1
    wcel
    #
    cB
    @18
    wceq
    @15
    @4
    @1
    @16
    @34
    sselda
    #
    cB
    @16
    toponuni
    syl
    @60
    @61
    @16
    ctop
    wcel
    @18
    @16
    wcel
    @62
    cB
    @16
    topontop
    @16
    @18
    @18
    eqid
    topopn
    3syl
    eqeltrd
    ralrimiva
    3adant1
    @0
    @9
    @49
    @59
    wb
    @10
    vc
    cB
    @4
    cV
    elintg
    3ad2ant1
    mpbird
    @12
    cB
    unissel
    syl2anc
    eqcomd
    cB
    @12
    istopon
    sylanbrc
    ismred
end
