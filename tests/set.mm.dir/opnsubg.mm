include "ctgp.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "w3a.mm"
include "ccld.mm"
include "cuni.mm"
include "wss.mm"
include "cdif.mm"
include "cbs.mm"
include "eqid.mm"
include "subgss.mm"
include "3ad2ant2.mm"
include "ctopon.mm"
include "wceq.mm"
include "tgptopon.mm"
include "3ad2ant1.mm"
include "toponuni.mm"
include "syl.mm"
include "sseqtrd.mm"
include "difeq1d.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "cplusg.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cima.mm"
include "cres.mm"
include "df-ima.mm"
include "adantr.mm"
include "resmptd.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "chmeo.mm"
include "simpl1.mm"
include "eldifi.mm"
include "adantl.mm"
include "tgplacthmeo.mm"
include "syl2anc.mm"
include "simpl3.mm"
include "hmeoima.mm"
include "eqeltrrd.mm"
include "c0g.mm"
include "cgrp.mm"
include "tgpgrp.mm"
include "grprid.mm"
include "cvv.mm"
include "simpl2.mm"
include "subg0cl.mm"
include "ovex.mm"
include "oveq2.mm"
include "elrnmpt1s.mm"
include "sylancl.mm"
include "wf.mm"
include "sselda.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "wn.mm"
include "eldifn.mm"
include "ad2antlr.mm"
include "csg.mm"
include "wi.mm"
include "subgsubcl.mm"
include "3com23.mm"
include "3expia.mm"
include "sylan.mm"
include "grppncan.mm"
include "eleq1d.mm"
include "sylibd.mm"
include "mtod.mm"
include "eldifd.mm"
include "fmptd.mm"
include "frn.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ralrimiva.mm"
include "ctop.mm"
include "wb.mm"
include "topontop.mm"
include "eltop2.mm"
include "mpbird.mm"
include "iscld.mm"
include "mpbir2and.mm"

theorem opnsubg
  let cS: class S
  let cG: class G
  let cJ: class J
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cR: class R
  let cX: class X
  assume subgntr.h: |- J = ( TopOpen ` G )


  assert |- ( ( G e. TopGrp /\ S e. ( SubGrp ` G ) /\ S e. J ) -> S e. ( Clsd ` J ) )

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
    cS
    cJ
    wcel
    #
    w3a
    #
    cS
    cJ
    ccld
    cfv
    wcel
    #
    cS
    cJ
    cuni
    #
    wss
    #
    @5
    cS
    cdif
    #
    cJ
    wcel
    #
    @3
    cS
    cG
    cbs
    cfv
    #
    @5
    @1
    @0
    cS
    @9
    wss
    #
    @2
    @9
    cS
    cG
    @9
    eqid
    #
    subgss
    3ad2ant2
    #
    @3
    cJ
    @9
    ctopon
    cfv
    wcel
    #
    @9
    @5
    wceq
    @0
    @1
    @13
    @2
    cG
    cJ
    @9
    subgntr.h
    @11
    tgptopon
    3ad2ant1
    #
    @9
    cJ
    toponuni
    syl
    #
    sseqtrd
    @3
    @9
    cS
    cdif
    #
    @7
    cJ
    @3
    @9
    @5
    cS
    @15
    difeq1d
    @3
    @16
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
    @19
    @16
    wss
    #
    wa
    #
    vu
    cJ
    wrex
    #
    vx
    @16
    wral
    #
    @3
    @23
    vx
    @16
    @3
    @18
    @16
    wcel
    #
    wa
    #
    vy
    cS
    @18
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
    @18
    @31
    wcel
    #
    @31
    @16
    wss
    #
    @23
    @26
    vy
    @9
    @29
    cmpt
    #
    cS
    cima
    #
    @31
    cJ
    @26
    @35
    @34
    cS
    cres
    #
    crn
    @31
    @34
    cS
    df-ima
    @26
    @36
    @30
    @26
    vy
    @9
    cS
    @29
    @3
    @10
    @25
    @12
    adantr
    #
    resmptd
    rneqd
    syl5eq
    @26
    @34
    cJ
    cJ
    chmeo
    co
    wcel
    #
    @2
    @35
    cJ
    wcel
    @26
    @0
    @18
    @9
    wcel
    #
    @38
    @0
    @1
    @2
    @25
    simpl1
    #
    @25
    @39
    @3
    @18
    @9
    cS
    eldifi
    adantl
    #
    vy
    @18
    @28
    @34
    cG
    cJ
    @9
    @34
    eqid
    @11
    @28
    eqid
    #
    subgntr.h
    tgplacthmeo
    syl2anc
    @0
    @1
    @2
    @25
    simpl3
    cS
    @34
    cJ
    cJ
    hmeoima
    syl2anc
    eqeltrrd
    @26
    @18
    cG
    c0g
    cfv
    #
    @28
    co
    #
    @18
    @31
    @26
    cG
    cgrp
    wcel
    #
    @39
    @44
    @18
    wceq
    @26
    @0
    @45
    @40
    cG
    tgpgrp
    syl
    #
    @41
    @9
    @28
    cG
    @18
    @43
    @11
    @42
    @43
    eqid
    #
    grprid
    syl2anc
    @26
    @43
    cS
    wcel
    #
    @44
    cvv
    wcel
    @44
    @31
    wcel
    @26
    @1
    @48
    @0
    @1
    @2
    @25
    simpl2
    #
    cS
    cG
    @43
    @47
    subg0cl
    syl
    @18
    @43
    @28
    ovex
    vy
    cS
    @29
    @44
    @43
    @30
    cvv
    @30
    eqid
    #
    @27
    @43
    @18
    @28
    oveq2
    elrnmpt1s
    sylancl
    eqeltrrd
    @26
    cS
    @16
    @30
    wf
    @33
    @26
    vy
    cS
    @29
    @16
    @30
    @26
    @27
    cS
    wcel
    #
    wa
    #
    @29
    @9
    cS
    @52
    @45
    @39
    @27
    @9
    wcel
    #
    @29
    @9
    wcel
    @26
    @45
    @51
    @46
    adantr
    #
    @26
    @39
    @51
    @41
    adantr
    #
    @26
    cS
    @9
    @27
    @37
    sselda
    #
    @9
    @28
    cG
    @18
    @27
    @11
    @42
    grpcl
    syl3anc
    @52
    @29
    cS
    wcel
    #
    @18
    cS
    wcel
    #
    @25
    @58
    wn
    @3
    @51
    @18
    @9
    cS
    eldifn
    ad2antlr
    @52
    @57
    @29
    @27
    cG
    csg
    cfv
    #
    co
    #
    cS
    wcel
    #
    @58
    @26
    @1
    @51
    @57
    @61
    wi
    @49
    @1
    @51
    @57
    @61
    @1
    @57
    @51
    @61
    cS
    cG
    @59
    @29
    @27
    @59
    eqid
    #
    subgsubcl
    3com23
    3expia
    sylan
    @52
    @60
    @18
    cS
    @52
    @45
    @39
    @53
    @60
    @18
    wceq
    @54
    @55
    @56
    @9
    @28
    cG
    @59
    @18
    @27
    @11
    @42
    @62
    grppncan
    syl3anc
    eleq1d
    sylibd
    mtod
    eldifd
    @50
    fmptd
    cS
    @16
    @30
    frn
    syl
    @22
    @32
    @33
    wa
    vu
    @31
    cJ
    @19
    @31
    wceq
    @20
    @32
    @21
    @33
    @19
    @31
    @18
    eleq2
    @19
    @31
    @16
    sseq1
    anbi12d
    rspcev
    syl12anc
    ralrimiva
    @3
    cJ
    ctop
    wcel
    #
    @17
    @24
    wb
    @3
    @13
    @63
    @14
    @9
    cJ
    topontop
    syl
    #
    vx
    vu
    @16
    cJ
    eltop2
    syl
    mpbird
    eqeltrrd
    @3
    @63
    @4
    @6
    @8
    wa
    wb
    @64
    cS
    cJ
    @5
    @5
    eqid
    iscld
    syl
    mpbir2and
end
