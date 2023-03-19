include "cv.mm"
include "cpw.mm"
include "cfn.mm"
include "wcel.mm"
include "csn.mm"
include "cun.mm"
include "cdif.mm"
include "pwundif.mm"
include "crn.mm"
include "cdom.mm"
include "wbr.mm"
include "wfo.mm"
include "wfn.mm"
include "vex.mm"
include "snex.mm"
include "unex.mm"
include "fnmpti.mm"
include "dffn4.mm"
include "mpbi.mm"
include "fodomfi.mm"
include "mpan2.mm"
include "domfi.mm"
include "mpdan.mm"
include "wss.mm"
include "wceq.mm"
include "wrex.mm"
include "eldifi.mm"
include "elpwun.mm"
include "sylib.mm"
include "undif1.mm"
include "elpwunsn.mm"
include "snssd.mm"
include "ssequn2.mm"
include "syl5req.mm"
include "uneq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "elrnmpti.mm"
include "sylibr.mm"
include "ssriv.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "unfi.mm"
include "mpancom.mm"
include "syl5eqel.mm"

theorem pwfilem
  let vx: setvar x
  let cF: class F
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume pwfilem.1: |- F = ( c e. ~P b |-> ( c u. { x } ) )

  disjoint b c
  disjoint c x
  disjoint F d
  disjoint c d
  disjoint b d
  disjoint d x
  assert |- ( ~P b e. Fin -> ~P ( b u. { x } ) e. Fin )

  proof
    vb
    cv
    #
    cpw
    #
    cfn
    wcel
    #
    @0
    vx
    cv
    #
    csn
    #
    cun
    cpw
    #
    @5
    @1
    cdif
    #
    @1
    cun
    #
    cfn
    @0
    @4
    pwundif
    @6
    cfn
    wcel
    #
    @2
    @7
    cfn
    wcel
    @2
    cF
    crn
    #
    cfn
    wcel
    #
    @6
    @9
    cdom
    wbr
    #
    @8
    @2
    @9
    @1
    cdom
    wbr
    #
    @10
    @2
    @1
    @9
    cF
    wfo
    #
    @12
    cF
    @1
    wfn
    @13
    vc
    @1
    vc
    cv
    #
    @4
    cun
    #
    cF
    @14
    @4
    vc
    vex
    @3
    snex
    #
    unex
    #
    pwfilem.1
    fnmpti
    @1
    cF
    dffn4
    mpbi
    @1
    @9
    cF
    fodomfi
    mpan2
    @1
    @9
    domfi
    mpdan
    #
    @2
    @10
    @6
    @9
    wss
    @11
    @18
    vd
    @6
    @9
    vd
    cv
    #
    @6
    wcel
    #
    @19
    @15
    wceq
    #
    vc
    @1
    wrex
    #
    @19
    @9
    wcel
    @20
    @19
    @4
    cdif
    #
    @1
    wcel
    #
    @19
    @23
    @4
    cun
    #
    wceq
    #
    @22
    @20
    @19
    @5
    wcel
    @24
    @19
    @5
    @1
    eldifi
    @19
    @0
    @4
    @16
    elpwun
    sylib
    @20
    @25
    @19
    @4
    cun
    #
    @19
    @19
    @4
    undif1
    @20
    @4
    @19
    wss
    @27
    @19
    wceq
    @20
    @3
    @19
    @19
    @0
    @3
    elpwunsn
    snssd
    @4
    @19
    ssequn2
    sylib
    syl5req
    @21
    @26
    vc
    @23
    @1
    @14
    @23
    wceq
    @15
    @25
    @19
    @14
    @23
    @4
    uneq1
    eqeq2d
    rspcev
    syl2anc
    vc
    @1
    @15
    @19
    cF
    pwfilem.1
    @17
    elrnmpti
    sylibr
    ssriv
    @6
    @9
    cfn
    ssdomg
    mpisyl
    @9
    @6
    domfi
    syl2anc
    @6
    @1
    unfi
    mpancom
    syl5eqel
end
