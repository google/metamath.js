include "ctgp.mm"
include "wcel.mm"
include "wa.mm"
include "cec.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "csn.mm"
include "cima.mm"
include "ccl.mm"
include "imaeq2i.mm"
include "cgrp.mm"
include "wss.mm"
include "wceq.mm"
include "tgpgrp.mm"
include "adantr.mm"
include "cuni.mm"
include "ctop.mm"
include "ctopon.mm"
include "tgptopon.mm"
include "topontop.mm"
include "syl.mm"
include "grpidcl.mm"
include "snssd.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "clsss3.mm"
include "syl2anc.mm"
include "sseqtr4d.mm"
include "syl5eqss.mm"
include "simpr.mm"
include "eqglact.mm"
include "syl3anc.mm"
include "chmeo.mm"
include "tgplacthmeo.mm"
include "hmeocls.mm"
include "3eqtr4a.mm"
include "crn.mm"
include "cres.mm"
include "df-ima.mm"
include "resmptd.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "wrex.mm"
include "cab.mm"
include "c0g.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rexsn.mm"
include "grprid.mm"
include "sylan.mm"
include "syl5bb.mm"
include "abbidv.mm"
include "rnmpt.mm"
include "df-sn.mm"
include "3eqtr4g.mm"
include "eqtrd.mm"
include "fveq2d.mm"

theorem snclseqg
  let cA: class A
  let c.sm: class .~
  let cS: class S
  let cG: class G
  let cJ: class J
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume snclseqg.x: |- X = ( Base ` G )
  assume snclseqg.j: |- J = ( TopOpen ` G )
  assume snclseqg.z: |- .0. = ( 0g ` G )
  assume snclseqg.r: |- .~ = ( G ~QG S )
  assume snclseqg.s: |- S = ( ( cls ` J ) ` { .0. } )


  assert |- ( ( G e. TopGrp /\ A e. X ) -> [ A ] .~ = ( ( cls ` J ) ` { A } ) )

  proof
    cG
    ctgp
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    c.sm
    cec
    #
    vx
    cX
    cA
    vx
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
    c.0
    csn
    #
    cima
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    cA
    csn
    #
    @10
    cfv
    @2
    @7
    cS
    cima
    #
    @7
    @8
    @10
    cfv
    #
    cima
    #
    @3
    @11
    cS
    @14
    @7
    snclseqg.s
    imaeq2i
    @2
    cG
    cgrp
    wcel
    #
    cS
    cX
    wss
    @1
    @3
    @13
    wceq
    @0
    @16
    @1
    cG
    tgpgrp
    #
    adantr
    #
    @2
    cS
    @14
    cX
    snclseqg.s
    @2
    @14
    cJ
    cuni
    #
    cX
    @2
    cJ
    ctop
    wcel
    #
    @8
    @19
    wss
    #
    @14
    @19
    wss
    @2
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @20
    @0
    @22
    @1
    cG
    cJ
    cX
    snclseqg.j
    snclseqg.x
    tgptopon
    adantr
    #
    cX
    cJ
    topontop
    syl
    @2
    @8
    cX
    @19
    @2
    c.0
    cX
    @2
    @16
    c.0
    cX
    wcel
    @18
    cX
    cG
    c.0
    snclseqg.x
    snclseqg.z
    grpidcl
    syl
    snssd
    #
    @2
    @22
    cX
    @19
    wceq
    @23
    cX
    cJ
    toponuni
    syl
    #
    sseqtrd
    #
    @8
    cJ
    @19
    @19
    eqid
    #
    clsss3
    syl2anc
    @25
    sseqtr4d
    syl5eqss
    @0
    @1
    simpr
    vx
    cA
    @5
    c.sm
    cG
    cX
    cS
    snclseqg.x
    snclseqg.r
    @5
    eqid
    #
    eqglact
    syl3anc
    @2
    @7
    cJ
    cJ
    chmeo
    co
    wcel
    @21
    @11
    @15
    wceq
    vx
    cA
    @5
    @7
    cG
    cJ
    cX
    @7
    eqid
    snclseqg.x
    @28
    snclseqg.j
    tgplacthmeo
    @26
    @8
    @7
    cJ
    cJ
    @19
    @27
    hmeocls
    syl2anc
    3eqtr4a
    @2
    @9
    @12
    @10
    @2
    @9
    vx
    @8
    @6
    cmpt
    #
    crn
    #
    @12
    @2
    @9
    @7
    @8
    cres
    #
    crn
    @30
    @7
    @8
    df-ima
    @2
    @31
    @29
    @2
    vx
    cX
    @8
    @6
    @24
    resmptd
    rneqd
    syl5eq
    @2
    vy
    cv
    #
    @6
    wceq
    #
    vx
    @8
    wrex
    #
    vy
    cab
    @32
    cA
    wceq
    #
    vy
    cab
    @30
    @12
    @2
    @34
    @35
    vy
    @34
    @32
    cA
    c.0
    @5
    co
    #
    wceq
    #
    @2
    @35
    @33
    @37
    vx
    c.0
    c.0
    cG
    c0g
    cfv
    cvv
    snclseqg.z
    cG
    c0g
    fvex
    eqeltri
    @4
    c.0
    wceq
    @6
    @36
    @32
    @4
    c.0
    cA
    @5
    oveq2
    eqeq2d
    rexsn
    @2
    @36
    cA
    @32
    @0
    @16
    @1
    @36
    cA
    wceq
    @17
    cX
    @5
    cG
    cA
    c.0
    snclseqg.x
    @28
    snclseqg.z
    grprid
    sylan
    eqeq2d
    syl5bb
    abbidv
    vx
    vy
    @8
    @6
    @29
    @29
    eqid
    rnmpt
    vy
    cA
    df-sn
    3eqtr4g
    eqtrd
    fveq2d
    eqtrd
end
