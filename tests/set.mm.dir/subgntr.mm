include "ctgp.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "cnt.mm"
include "w3a.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "csg.mm"
include "co.mm"
include "cplusg.mm"
include "cmpt.mm"
include "crn.mm"
include "cbs.mm"
include "cima.mm"
include "cres.mm"
include "df-ima.mm"
include "ctopon.mm"
include "eqid.mm"
include "tgptopon.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "ctop.mm"
include "cuni.mm"
include "topontop.mm"
include "syl.mm"
include "simpl2.mm"
include "subgss.mm"
include "wceq.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "ntropn.mm"
include "syl2anc.mm"
include "toponss.mm"
include "resmptd.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "chmeo.mm"
include "simpl1.mm"
include "simpr.mm"
include "ntrss2.mm"
include "simpl3.mm"
include "sseldd.mm"
include "subgsubcl.mm"
include "syl3anc.mm"
include "tgplacthmeo.mm"
include "hmeoima.mm"
include "eqeltrrd.mm"
include "cgrp.mm"
include "tgpgrp.mm"
include "3ad2ant2.mm"
include "sselda.mm"
include "grpnpcan.mm"
include "cvv.mm"
include "ovex.mm"
include "oveq2.mm"
include "elrnmpt1s.mm"
include "sylancl.mm"
include "wf.mm"
include "subgcl.mm"
include "fmptd.mm"
include "frn.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ralrimiva.mm"
include "wb.mm"
include "eltop2.mm"
include "mpbird.mm"

theorem subgntr
  let cA: class A
  let cS: class S
  let cG: class G
  let cJ: class J
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cX: class X
  assume subgntr.h: |- J = ( TopOpen ` G )


  assert |- ( ( G e. TopGrp /\ S e. ( SubGrp ` G ) /\ A e. ( ( int ` J ) ` S ) ) -> S e. J )

  proof
    cG
    ctgp
    wcel
    #
    cS
    cG
    csubg
    cfv
    wcel
    #
    cA
    cS
    cJ
    cnt
    cfv
    cfv
    #
    wcel
    #
    w3a
    #
    cS
    cJ
    wcel
    #
    vx
    cv
    #
    vu
    cv
    #
    wcel
    #
    @7
    cS
    wss
    #
    wa
    #
    vu
    cJ
    wrex
    #
    vx
    cS
    wral
    #
    @4
    @11
    vx
    cS
    @4
    @6
    cS
    wcel
    #
    wa
    #
    vy
    @2
    @6
    cA
    cG
    csg
    cfv
    #
    co
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    cJ
    wcel
    @6
    @21
    wcel
    #
    @21
    cS
    wss
    #
    @11
    @14
    vy
    cG
    cbs
    cfv
    #
    @19
    cmpt
    #
    @2
    cima
    #
    @21
    cJ
    @14
    @26
    @25
    @2
    cres
    #
    crn
    @21
    @25
    @2
    df-ima
    @14
    @27
    @20
    @14
    vy
    @24
    @2
    @19
    @14
    cJ
    @24
    ctopon
    cfv
    wcel
    #
    @2
    cJ
    wcel
    #
    @2
    @24
    wss
    @4
    @28
    @13
    @0
    @1
    @28
    @3
    cG
    cJ
    @24
    subgntr.h
    @24
    eqid
    #
    tgptopon
    3ad2ant1
    #
    adantr
    #
    @14
    cJ
    ctop
    wcel
    #
    cS
    cJ
    cuni
    #
    wss
    #
    @29
    @4
    @33
    @13
    @4
    @28
    @33
    @31
    @24
    cJ
    topontop
    syl
    #
    adantr
    #
    @14
    cS
    @24
    @34
    @14
    @1
    cS
    @24
    wss
    #
    @0
    @1
    @3
    @13
    simpl2
    #
    @24
    cS
    cG
    @30
    subgss
    #
    syl
    #
    @14
    @28
    @24
    @34
    wceq
    @32
    @24
    cJ
    toponuni
    syl
    sseqtrd
    #
    cS
    cJ
    @34
    @34
    eqid
    #
    ntropn
    syl2anc
    #
    @2
    cJ
    @24
    toponss
    syl2anc
    #
    resmptd
    rneqd
    syl5eq
    @14
    @25
    cJ
    cJ
    chmeo
    co
    wcel
    #
    @29
    @26
    cJ
    wcel
    @14
    @0
    @16
    @24
    wcel
    @46
    @0
    @1
    @3
    @13
    simpl1
    #
    @14
    cS
    @24
    @16
    @41
    @14
    @1
    @13
    cA
    cS
    wcel
    @16
    cS
    wcel
    #
    @39
    @4
    @13
    simpr
    @14
    @2
    cS
    cA
    @14
    @33
    @35
    @2
    cS
    wss
    @37
    @42
    cS
    cJ
    @34
    @43
    ntrss2
    syl2anc
    #
    @0
    @1
    @3
    @13
    simpl3
    #
    sseldd
    cS
    cG
    @15
    @6
    cA
    @15
    eqid
    #
    subgsubcl
    syl3anc
    #
    sseldd
    vy
    @16
    @18
    @25
    cG
    cJ
    @24
    @25
    eqid
    @30
    @18
    eqid
    #
    subgntr.h
    tgplacthmeo
    syl2anc
    @44
    @2
    @25
    cJ
    cJ
    hmeoima
    syl2anc
    eqeltrrd
    @14
    @16
    cA
    @18
    co
    #
    @6
    @21
    @14
    cG
    cgrp
    wcel
    #
    @6
    @24
    wcel
    cA
    @24
    wcel
    @54
    @6
    wceq
    @14
    @0
    @55
    @47
    cG
    tgpgrp
    syl
    @4
    cS
    @24
    @6
    @1
    @0
    @38
    @3
    @40
    3ad2ant2
    sselda
    @14
    @2
    @24
    cA
    @45
    @50
    sseldd
    @24
    @18
    cG
    @15
    @6
    cA
    @30
    @53
    @51
    grpnpcan
    syl3anc
    @14
    @3
    @54
    cvv
    wcel
    @54
    @21
    wcel
    @50
    @16
    cA
    @18
    ovex
    vy
    @2
    @19
    @54
    cA
    @20
    cvv
    @20
    eqid
    #
    @17
    cA
    @16
    @18
    oveq2
    elrnmpt1s
    sylancl
    eqeltrrd
    @14
    @2
    cS
    @20
    wf
    @23
    @14
    vy
    @2
    @19
    cS
    @20
    @14
    @17
    @2
    wcel
    #
    wa
    @1
    @48
    @17
    cS
    wcel
    @19
    cS
    wcel
    @14
    @1
    @57
    @39
    adantr
    @14
    @48
    @57
    @52
    adantr
    @14
    @2
    cS
    @17
    @49
    sselda
    @18
    cS
    cG
    @16
    @17
    @53
    subgcl
    syl3anc
    @56
    fmptd
    @2
    cS
    @20
    frn
    syl
    @10
    @22
    @23
    wa
    vu
    @21
    cJ
    @7
    @21
    wceq
    @8
    @22
    @9
    @23
    @7
    @21
    @6
    eleq2
    @7
    @21
    cS
    sseq1
    anbi12d
    rspcev
    syl12anc
    ralrimiva
    @4
    @33
    @5
    @12
    wb
    @36
    vx
    vu
    cS
    cJ
    eltop2
    syl
    mpbird
end
