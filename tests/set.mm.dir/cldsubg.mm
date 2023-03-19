include "ctgp.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "cqs.mm"
include "cfn.mm"
include "w3a.mm"
include "ccld.mm"
include "wa.mm"
include "cuni.mm"
include "csn.mm"
include "cdif.mm"
include "ctopon.mm"
include "wceq.mm"
include "simpl1.mm"
include "tgptopon.mm"
include "syl.mm"
include "toponuni.mm"
include "difeq1d.mm"
include "cun.mm"
include "simpl2.mm"
include "unisng.mm"
include "uneq2d.mm"
include "uniun.mm"
include "undif1.mm"
include "wss.mm"
include "c0g.mm"
include "cec.mm"
include "eqid.mm"
include "eqgid.mm"
include "cvv.mm"
include "cqg.mm"
include "co.mm"
include "ovex.mm"
include "eqeltri.mm"
include "cgrp.mm"
include "tgpgrp.mm"
include "grpidcl.mm"
include "ecelqsg.mm"
include "sylancr.mm"
include "eqeltrrd.mm"
include "snssd.mm"
include "ssequn2.mm"
include "sylib.mm"
include "syl5eq.mm"
include "unieqd.mm"
include "wer.mm"
include "eqger.mm"
include "a1i.mm"
include "uniqs2.mm"
include "eqtrd.mm"
include "syl5eqr.mm"
include "eqtr3d.mm"
include "cin.mm"
include "c0.mm"
include "wb.mm"
include "difss.mm"
include "unissi.mm"
include "syl5sseq.mm"
include "cpw.mm"
include "cv.mm"
include "wne.mm"
include "wn.mm"
include "df-ne.mm"
include "adantr.mm"
include "simpr.mm"
include "qsdisj.mm"
include "ord.mm"
include "disj2.mm"
include "syl6ib.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "eldifsn.mm"
include "selpw.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "sspwuni.mm"
include "sylibr.mm"
include "uneqdifeq.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "ctop.mm"
include "topontop.mm"
include "simpl3.mm"
include "diffi.mm"
include "wrex.mm"
include "vex.mm"
include "elqs.mm"
include "cplusg.mm"
include "cmpt.mm"
include "cima.mm"
include "simpll2.mm"
include "subgrcl.mm"
include "subgss.mm"
include "eqglact.mm"
include "syl3anc.mm"
include "simplr.mm"
include "chmeo.mm"
include "tgplacthmeo.mm"
include "sylan.mm"
include "sseqtrd.mm"
include "hmeocld.mm"
include "eqeltrd.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "ssdifssd.mm"
include "unicld.mm"
include "cldopn.mm"
include "ex.mm"
include "wi.mm"
include "opnsubg.mm"
include "3expia.mm"
include "3adant3.mm"
include "impbid.mm"

theorem cldsubg
  let cR: class R
  let cS: class S
  let cG: class G
  let cJ: class J
  let cX: class X
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume subgntr.h: |- J = ( TopOpen ` G )
  assume cldsubg.1: |- R = ( G ~QG S )
  assume cldsubg.2: |- X = ( Base ` G )


  assert |- ( ( G e. TopGrp /\ S e. ( SubGrp ` G ) /\ ( X /. R ) e. Fin ) -> ( S e. ( Clsd ` J ) <-> S e. J ) )

  proof
    cG
    ctgp
    wcel
    #
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cX
    cR
    cqs
    #
    cfn
    wcel
    #
    w3a
    #
    cS
    cJ
    ccld
    cfv
    #
    wcel
    #
    cS
    cJ
    wcel
    #
    @5
    @7
    @8
    @5
    @7
    wa
    #
    cJ
    cuni
    #
    @3
    cS
    csn
    #
    cdif
    #
    cuni
    #
    cdif
    #
    cS
    cJ
    @9
    cX
    @13
    cdif
    #
    @14
    cS
    @9
    cX
    @10
    @13
    @9
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cX
    @10
    wceq
    @9
    @0
    @16
    @0
    @2
    @4
    @7
    simpl1
    #
    cG
    cJ
    cX
    subgntr.h
    cldsubg.2
    tgptopon
    syl
    #
    cX
    cJ
    toponuni
    syl
    #
    difeq1d
    @9
    @13
    cS
    cun
    #
    cX
    wceq
    #
    @15
    cS
    wceq
    #
    @9
    @13
    @11
    cuni
    #
    cun
    #
    @20
    cX
    @9
    @23
    cS
    @13
    @9
    @2
    @23
    cS
    wceq
    @0
    @2
    @4
    @7
    simpl2
    #
    cS
    @1
    unisng
    syl
    uneq2d
    @9
    @24
    @12
    @11
    cun
    #
    cuni
    #
    cX
    @12
    @11
    uniun
    @9
    @27
    @3
    cuni
    #
    cX
    @9
    @26
    @3
    @9
    @26
    @3
    @11
    cun
    #
    @3
    @3
    @11
    undif1
    @9
    @11
    @3
    wss
    @29
    @3
    wceq
    @9
    cS
    @3
    @9
    cG
    c0g
    cfv
    #
    cR
    cec
    #
    cS
    @3
    @9
    @2
    @31
    cS
    wceq
    @25
    cR
    cG
    cX
    cS
    @30
    cldsubg.2
    cldsubg.1
    @30
    eqid
    #
    eqgid
    syl
    @9
    cR
    cvv
    wcel
    #
    @30
    cX
    wcel
    #
    @31
    @3
    wcel
    cR
    cG
    cS
    cqg
    co
    cvv
    cldsubg.1
    cG
    cS
    cqg
    ovex
    eqeltri
    #
    @9
    cG
    cgrp
    wcel
    #
    @34
    @9
    @0
    @36
    @17
    cG
    tgpgrp
    syl
    cX
    cG
    @30
    cldsubg.2
    @32
    grpidcl
    syl
    cX
    @30
    cR
    cvv
    ecelqsg
    sylancr
    eqeltrrd
    #
    snssd
    @11
    @3
    ssequn2
    sylib
    syl5eq
    unieqd
    @9
    cX
    cR
    cvv
    @9
    @2
    cX
    cR
    wer
    #
    @25
    cR
    cG
    cX
    cS
    cldsubg.2
    cldsubg.1
    eqger
    syl
    #
    @33
    @9
    @35
    a1i
    uniqs2
    #
    eqtrd
    syl5eqr
    eqtr3d
    @9
    @13
    cX
    wss
    @13
    cS
    cin
    c0
    wceq
    #
    @21
    @22
    wb
    @9
    @28
    @13
    cX
    @12
    @3
    @3
    @11
    difss
    unissi
    @40
    syl5sseq
    @9
    @13
    cvv
    cS
    cdif
    #
    wss
    #
    @41
    @9
    @12
    @42
    cpw
    #
    wss
    @43
    @9
    vx
    @12
    @44
    @9
    vx
    cv
    #
    @3
    wcel
    #
    @45
    cS
    wne
    #
    wa
    @45
    @42
    wss
    #
    @45
    @12
    wcel
    @45
    @44
    wcel
    @9
    @46
    @47
    @48
    @47
    @45
    cS
    wceq
    #
    wn
    #
    @9
    @46
    wa
    #
    @48
    @45
    cS
    df-ne
    @51
    @50
    @45
    cS
    cin
    c0
    wceq
    #
    @48
    @51
    @49
    @52
    @51
    cX
    @45
    cS
    cR
    cX
    @9
    @38
    @46
    @39
    adantr
    @9
    @46
    simpr
    @9
    cS
    @3
    wcel
    @46
    @37
    adantr
    qsdisj
    ord
    @45
    cS
    disj2
    syl6ib
    syl5bi
    expimpd
    @45
    @3
    cS
    eldifsn
    vx
    @42
    selpw
    3imtr4g
    ssrdv
    @12
    @42
    sspwuni
    sylib
    @13
    cS
    disj2
    sylibr
    @13
    cS
    cX
    uneqdifeq
    syl2anc
    mpbid
    eqtr3d
    @9
    @13
    @6
    wcel
    #
    @14
    cJ
    wcel
    @9
    cJ
    ctop
    wcel
    #
    @12
    cfn
    wcel
    #
    @12
    @6
    wss
    @53
    @9
    @16
    @54
    @18
    cX
    cJ
    topontop
    syl
    @9
    @4
    @55
    @0
    @2
    @4
    @7
    simpl3
    @3
    @11
    diffi
    syl
    @9
    @3
    @6
    @11
    @9
    vx
    @3
    @6
    @46
    @45
    vy
    cv
    #
    cR
    cec
    #
    wceq
    #
    vy
    cX
    wrex
    @9
    @45
    @6
    wcel
    #
    vy
    cX
    @45
    cR
    vx
    vex
    elqs
    @9
    @58
    @59
    vy
    cX
    @9
    @56
    cX
    wcel
    #
    wa
    #
    @59
    @58
    @57
    @6
    wcel
    @61
    @57
    vz
    cX
    @56
    vz
    cv
    cG
    cplusg
    cfv
    #
    co
    cmpt
    #
    cS
    cima
    #
    @6
    @61
    @36
    cS
    cX
    wss
    #
    @60
    @57
    @64
    wceq
    @61
    @2
    @36
    @0
    @2
    @4
    @7
    @60
    simpll2
    cS
    cG
    subgrcl
    syl
    @9
    @65
    @60
    @9
    @2
    @65
    @25
    cX
    cS
    cG
    cldsubg.2
    subgss
    syl
    #
    adantr
    @9
    @60
    simpr
    vz
    @56
    @62
    cR
    cG
    cX
    cS
    cldsubg.2
    cldsubg.1
    @62
    eqid
    #
    eqglact
    syl3anc
    @61
    @7
    @64
    @6
    wcel
    #
    @5
    @7
    @60
    simplr
    @61
    @63
    cJ
    cJ
    chmeo
    co
    wcel
    #
    cS
    @10
    wss
    #
    @7
    @68
    wb
    @9
    @0
    @60
    @69
    @17
    vz
    @56
    @62
    @63
    cG
    cJ
    cX
    @63
    eqid
    cldsubg.2
    @67
    subgntr.h
    tgplacthmeo
    sylan
    @9
    @70
    @60
    @9
    cS
    cX
    @10
    @66
    @19
    sseqtrd
    adantr
    cS
    @63
    cJ
    cJ
    @10
    @10
    eqid
    #
    hmeocld
    syl2anc
    mpbid
    eqeltrd
    @45
    @57
    @6
    eleq1
    syl5ibrcom
    rexlimdva
    syl5bi
    ssrdv
    ssdifssd
    @12
    cJ
    @10
    @71
    unicld
    syl3anc
    @13
    cJ
    @10
    @71
    cldopn
    syl
    eqeltrrd
    ex
    @0
    @2
    @8
    @7
    wi
    @4
    @0
    @2
    @8
    @7
    cS
    cG
    cJ
    subgntr.h
    opnsubg
    3expia
    3adant3
    impbid
end
