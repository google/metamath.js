include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "cxp.mm"
include "cmpt2.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "ctx.mm"
include "co.mm"
include "cvv.mm"
include "eqid.mm"
include "txbasex.mm"
include "adantr.mm"
include "cres.mm"
include "resmpt2.mm"
include "resss.mm"
include "syl6eqssr.mm"
include "adantl.mm"
include "rnss.mm"
include "syl.mm"
include "tgss.mm"
include "syl2anc.mm"
include "wceq.mm"
include "ssexg.mm"
include "txval.mm"
include "syl2an.mm"
include "an4s.mm"
include "ancoms.mm"
include "3sstr4d.mm"

theorem txss12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let cR: class R
  let cS: class S


  assert |- ( ( ( B e. V /\ D e. W ) /\ ( A C_ B /\ C C_ D ) ) -> ( A tX C ) C_ ( B tX D ) )

  proof
    cB
    cV
    wcel
    #
    cD
    cW
    wcel
    #
    wa
    #
    cA
    cB
    wss
    #
    cC
    cD
    wss
    #
    wa
    #
    wa
    #
    vx
    vy
    cA
    cC
    vx
    cv
    vy
    cv
    cxp
    #
    cmpt2
    #
    crn
    #
    ctg
    cfv
    #
    vx
    vy
    cB
    cD
    @7
    cmpt2
    #
    crn
    #
    ctg
    cfv
    #
    cA
    cC
    ctx
    co
    #
    cB
    cD
    ctx
    co
    #
    @6
    @12
    cvv
    wcel
    #
    @9
    @12
    wss
    #
    @10
    @13
    wss
    @2
    @16
    @5
    vx
    vy
    @12
    cB
    cD
    cV
    cW
    @12
    eqid
    #
    txbasex
    adantr
    @6
    @8
    @11
    wss
    #
    @17
    @5
    @19
    @2
    @5
    @8
    @11
    cA
    cC
    cxp
    #
    cres
    @11
    vx
    vy
    cB
    cD
    cA
    cC
    @7
    resmpt2
    @11
    @20
    resss
    syl6eqssr
    adantl
    @8
    @11
    rnss
    syl
    @9
    @12
    cvv
    tgss
    syl2anc
    @5
    @2
    @14
    @10
    wceq
    #
    @3
    @0
    @4
    @1
    @21
    @3
    @0
    wa
    cA
    cvv
    wcel
    cC
    cvv
    wcel
    @21
    @4
    @1
    wa
    cA
    cB
    cV
    ssexg
    cC
    cD
    cW
    ssexg
    vx
    vy
    @9
    cA
    cC
    cvv
    cvv
    @9
    eqid
    txval
    syl2an
    an4s
    ancoms
    @2
    @15
    @13
    wceq
    @5
    vx
    vy
    @12
    cB
    cD
    cV
    cW
    @18
    txval
    adantr
    3sstr4d
end
