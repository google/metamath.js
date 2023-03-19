include "wcel.mm"
include "wf1.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wceq.mm"
include "eqid.mm"
include "pm3.2i.mm"
include "cvv.mm"
include "elex.mm"
include "adantr.mm"
include "cv.mm"
include "wss.mm"
include "cxp.mm"
include "wwe.mm"
include "w3a.mm"
include "cop.mm"
include "df-ov.mm"
include "wf.mm"
include "f1f.mm"
include "ad2antlr.mm"
include "copab.mm"
include "simpr.mm"
include "opabid.mm"
include "sylibr.mm"
include "syl6eleqr.mm"
include "ffvelrnd.mm"
include "syl5eqel.mm"
include "fpwwe2.mm"
include "mpbiri.mm"
include "simprd.mm"
include "cin.mm"
include "xpeq12i.mm"
include "ineq2i.mm"
include "oveq12i.mm"
include "simpld.mm"
include "fpwwe2lem3.mm"
include "mpdan.mm"
include "syl5eq.mm"
include "3eqtr3g.mm"
include "wb.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wsbc.mm"
include "wral.mm"
include "fpwwe2lem2.mm"
include "mpbid.mm"
include "dmss.mm"
include "syl.mm"
include "dmxpss.mm"
include "syl6ss.mm"
include "syl5ss.mm"
include "syl5eqss.mm"
include "sstrd.mm"
include "inss2.mm"
include "a1i.mm"
include "wess.mm"
include "sylc.mm"
include "weinxp.mm"
include "sylib.mm"
include "fvex.mm"
include "cnvex.mm"
include "imaex.mm"
include "eqeltri.mm"
include "inex1.mm"
include "simpl.mm"
include "sseq1d.mm"
include "sqxpeqd.mm"
include "sseq12d.mm"
include "weeq2.mm"
include "weeq1.mm"
include "sylan9bb.mm"
include "3anbi123d.mm"
include "opelopaba.mm"
include "syl3anbrc.mm"
include "ssexd.mm"
include "opelopabga.mm"
include "syl2anc.mm"
include "mpbir3and.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "opth1.mm"
include "eleqtrrd.mm"
include "syl6eleq.mm"
include "ovex.mm"
include "eliniseg.mm"
include "wor.mm"
include "wn.mm"
include "weso.mm"
include "sonr.mm"
include "pm2.65da.mm"

theorem canthwelem
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cO: class O
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vf: setvar f
  let vv: setvar v
  let vw: setvar w
  let va: setvar a
  let vs: setvar s
  let vz: setvar z
  assume canthwe.1: |- O = { <. x , r >. | ( x C_ A /\ r C_ ( x X. x ) /\ r We x ) }
  assume canthwe.2: |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\ ( r We x /\ A. y e. x [. ( `' r " { y } ) / u ]. ( u F ( r i^i ( u X. u ) ) ) = y ) ) }
  assume canthwe.3: |- B = U. dom W
  assume canthwe.4: |- C = ( `' ( W ` B ) " { ( B F ( W ` B ) ) } )

  disjoint r u
  disjoint r x
  disjoint r y
  disjoint B r
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C r
  disjoint C x
  disjoint O r
  disjoint O u
  disjoint O x
  disjoint O y
  disjoint V r
  disjoint V u
  disjoint V x
  disjoint V y
  disjoint A r
  disjoint A u
  disjoint A x
  disjoint A y
  disjoint F r
  disjoint F u
  disjoint F x
  disjoint F y
  disjoint W r
  disjoint W u
  disjoint W x
  disjoint W y
  disjoint f r
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint O f
  disjoint r v
  disjoint r w
  disjoint u v
  disjoint u w
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint O v
  disjoint w x
  disjoint w y
  disjoint O w
  disjoint V f
  disjoint V v
  disjoint V w
  disjoint a f
  disjoint a r
  disjoint a s
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint f s
  disjoint f z
  disjoint r s
  disjoint r z
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint v z
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint a u
  disjoint A a
  disjoint A f
  disjoint s u
  disjoint A s
  disjoint A v
  disjoint A w
  assert |- ( A e. V -> -. F : O -1-1-> A )

  proof
    cA
    cV
    wcel
    #
    cO
    cA
    cF
    wf1
    #
    cB
    cB
    cW
    cfv
    #
    cF
    co
    #
    @3
    @2
    wbr
    #
    @0
    @1
    wa
    #
    @3
    @2
    ccnv
    #
    @3
    csn
    #
    cima
    #
    wcel
    #
    @4
    @5
    @3
    cC
    @8
    @5
    @3
    cB
    cC
    @5
    cB
    @2
    cW
    wbr
    #
    @3
    cB
    wcel
    #
    @5
    @10
    @11
    wa
    cB
    cB
    wceq
    #
    @2
    @2
    wceq
    #
    wa
    @12
    @13
    cB
    eqid
    @2
    eqid
    pm3.2i
    @5
    vx
    vy
    vu
    cA
    @2
    cF
    cW
    cB
    cB
    vr
    canthwe.2
    @0
    cA
    cvv
    wcel
    @1
    cA
    cV
    elex
    adantr
    #
    @5
    vx
    cv
    #
    cA
    wss
    #
    vr
    cv
    #
    @15
    @15
    cxp
    #
    wss
    #
    @15
    @17
    wwe
    #
    w3a
    #
    wa
    #
    @15
    @17
    cF
    co
    @15
    @17
    cop
    #
    cF
    cfv
    cA
    @15
    @17
    cF
    df-ov
    @22
    cO
    cA
    @23
    cF
    @1
    cO
    cA
    cF
    wf
    @0
    @21
    cO
    cA
    cF
    f1f
    ad2antlr
    @22
    @23
    @21
    vx
    vr
    copab
    #
    cO
    @22
    @21
    @23
    @24
    wcel
    @5
    @21
    simpr
    @21
    vx
    vr
    opabid
    sylibr
    canthwe.1
    syl6eleqr
    ffvelrnd
    syl5eqel
    canthwe.3
    fpwwe2
    mpbiri
    #
    simprd
    #
    @5
    cC
    @2
    cC
    cC
    cxp
    #
    cin
    #
    cop
    #
    cB
    @2
    cop
    #
    wceq
    #
    cC
    cB
    wceq
    @5
    @29
    cF
    cfv
    #
    @30
    cF
    cfv
    #
    wceq
    #
    @31
    @5
    cC
    @28
    cF
    co
    #
    @3
    @32
    @33
    @5
    @35
    @8
    @2
    @8
    @8
    cxp
    #
    cin
    #
    cF
    co
    #
    @3
    cC
    @8
    @28
    @37
    cF
    canthwe.4
    @27
    @36
    @2
    cC
    @8
    cC
    @8
    canthwe.4
    canthwe.4
    xpeq12i
    ineq2i
    oveq12i
    @5
    @11
    @38
    @3
    wceq
    @26
    @5
    vx
    vy
    vu
    cA
    @3
    @2
    cF
    cW
    cB
    vr
    canthwe.2
    @14
    @5
    @10
    @11
    @25
    simpld
    #
    fpwwe2lem3
    mpdan
    syl5eq
    cC
    @28
    cF
    df-ov
    cB
    @2
    cF
    df-ov
    3eqtr3g
    @5
    @1
    @29
    cO
    wcel
    @30
    cO
    wcel
    @34
    @31
    wb
    @0
    @1
    simpr
    @5
    @29
    @24
    cO
    @5
    cC
    cA
    wss
    #
    @28
    @27
    wss
    #
    cC
    @28
    wwe
    #
    @29
    @24
    wcel
    @5
    cC
    cB
    cA
    @5
    cC
    @8
    cB
    canthwe.4
    @5
    @8
    @2
    cdm
    #
    cB
    @2
    @7
    cnvimass
    @5
    @43
    cB
    cB
    cxp
    #
    cdm
    #
    cB
    @5
    @2
    @44
    wss
    #
    @43
    @45
    wss
    @5
    cB
    cA
    wss
    #
    @46
    @5
    @47
    @46
    wa
    #
    cB
    @2
    wwe
    #
    vu
    cv
    #
    @2
    @50
    @50
    cxp
    cin
    cF
    co
    vy
    cv
    #
    wceq
    vu
    @6
    @51
    csn
    cima
    wsbc
    vy
    cB
    wral
    #
    wa
    #
    @5
    @10
    @48
    @53
    wa
    @39
    @5
    vx
    vy
    vu
    cA
    @2
    cF
    cW
    cB
    vr
    canthwe.2
    @14
    fpwwe2lem2
    mpbid
    #
    simpld
    #
    simprd
    #
    @2
    @44
    dmss
    syl
    cB
    cB
    dmxpss
    syl6ss
    syl5ss
    syl5eqss
    #
    @5
    @47
    @46
    @55
    simpld
    #
    sstrd
    @41
    @5
    @2
    @27
    inss2
    a1i
    @5
    cC
    @2
    wwe
    #
    @42
    @5
    cC
    cB
    wss
    @49
    @59
    @57
    @5
    @49
    @52
    @5
    @48
    @53
    @54
    simprd
    simpld
    #
    cC
    cB
    @2
    wess
    sylc
    cC
    @2
    weinxp
    sylib
    @21
    @40
    @41
    @42
    w3a
    vx
    vr
    cC
    @28
    cC
    @8
    cvv
    canthwe.4
    @6
    @7
    @2
    cB
    cW
    fvex
    #
    cnvex
    imaex
    eqeltri
    #
    @2
    @27
    @61
    inex1
    #
    @15
    cC
    wceq
    #
    @17
    @28
    wceq
    #
    wa
    #
    @16
    @40
    @19
    @41
    @20
    @42
    @66
    @15
    cC
    cA
    @64
    @65
    simpl
    #
    sseq1d
    @66
    @17
    @28
    @18
    @27
    @64
    @65
    simpr
    @66
    @15
    cC
    @67
    sqxpeqd
    sseq12d
    @64
    @20
    cC
    @17
    wwe
    @65
    @42
    @15
    cC
    @17
    weeq2
    cC
    @17
    @28
    weeq1
    sylan9bb
    3anbi123d
    opelopaba
    syl3anbrc
    canthwe.1
    syl6eleqr
    @5
    @30
    @24
    cO
    @5
    @30
    @24
    wcel
    #
    @47
    @46
    @49
    @58
    @56
    @60
    @5
    cB
    cvv
    wcel
    @2
    cvv
    wcel
    #
    @68
    @47
    @46
    @49
    w3a
    #
    wb
    @5
    cB
    cA
    cvv
    @14
    @58
    ssexd
    @69
    @5
    @61
    a1i
    @21
    @70
    vx
    vr
    cB
    @2
    cvv
    cvv
    @15
    cB
    wceq
    #
    @17
    @2
    wceq
    #
    wa
    #
    @16
    @47
    @19
    @46
    @20
    @49
    @73
    @15
    cB
    cA
    @71
    @72
    simpl
    #
    sseq1d
    @73
    @17
    @2
    @18
    @44
    @71
    @72
    simpr
    @73
    @15
    cB
    @74
    sqxpeqd
    sseq12d
    @71
    @20
    cB
    @17
    wwe
    @72
    @49
    @15
    cB
    @17
    weeq2
    cB
    @17
    @2
    weeq1
    sylan9bb
    3anbi123d
    opelopabga
    syl2anc
    mpbir3and
    canthwe.1
    syl6eleqr
    cO
    cA
    @29
    @30
    cF
    f1fveq
    syl12anc
    mpbid
    cC
    @28
    cB
    @2
    @62
    @63
    opth1
    syl
    eleqtrrd
    canthwe.4
    syl6eleq
    @5
    @11
    @9
    @4
    wb
    @26
    @2
    @3
    @3
    cB
    cB
    @2
    cF
    ovex
    eliniseg
    syl
    mpbid
    @5
    cB
    @2
    wor
    #
    @11
    @4
    wn
    @5
    @49
    @75
    @60
    cB
    @2
    weso
    syl
    @26
    cB
    @3
    @2
    sonr
    syl2anc
    pm2.65da
end
