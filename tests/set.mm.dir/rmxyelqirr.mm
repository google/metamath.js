include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cpell14qr.mm"
include "cv.mm"
include "csqrt.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "cn0.mm"
include "cab.mm"
include "cr.mm"
include "crab.mm"
include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "rmspecnonsq.mm"
include "adantr.mm"
include "pell14qrval.mm"
include "syl.mm"
include "cvv.mm"
include "wi.mm"
include "wral.mm"
include "wss.mm"
include "simpl.mm"
include "reximi.mm"
include "rgenw.mm"
include "a1i.mm"
include "ss2rab.mm"
include "sylibr.mm"
include "ssv.mm"
include "rabss2.mm"
include "ax-mp.mm"
include "syl6ss.mm"
include "rabab.mm"
include "syl6sseq.mm"
include "eqsstrd.mm"
include "cpellfund.mm"
include "simpr.mm"
include "rmspecfund.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "pellfund14b.mm"
include "mpbird.mm"
include "sseldd.mm"

theorem rmxyelqirr
  let cA: class A
  let cN: class N
  let va: setvar a
  let vc: setvar c
  let vd: setvar d

  disjoint A a
  disjoint A c
  disjoint A d
  disjoint a c
  disjoint a d
  disjoint c d
  disjoint N a
  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( ( A + ( sqrt ` ( ( A ^ 2 ) - 1 ) ) ) ^ N ) e. { a | E. c e. NN0 E. d e. ZZ a = ( c + ( ( sqrt ` ( ( A ^ 2 ) - 1 ) ) x. d ) ) } )

  proof
    cA
    c2
    cuz
    cfv
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cA
    c2
    cexp
    co
    c1
    cmin
    co
    #
    cpell14qr
    cfv
    #
    va
    cv
    #
    vc
    cv
    #
    @3
    csqrt
    cfv
    #
    vd
    cv
    #
    cmul
    co
    caddc
    co
    wceq
    #
    vd
    cz
    wrex
    #
    vc
    cn0
    wrex
    #
    va
    cab
    #
    cA
    @7
    caddc
    co
    #
    cN
    cexp
    co
    #
    @2
    @4
    @9
    @6
    c2
    cexp
    co
    @3
    @8
    c2
    cexp
    co
    cmul
    co
    cmin
    co
    c1
    wceq
    #
    wa
    #
    vd
    cz
    wrex
    #
    vc
    cn0
    wrex
    #
    va
    cr
    crab
    #
    @12
    @2
    @3
    cn
    csquarenn
    cdif
    wcel
    #
    @4
    @19
    wceq
    @0
    @20
    @1
    cA
    rmspecnonsq
    adantr
    #
    va
    vc
    vd
    @3
    pell14qrval
    syl
    @2
    @19
    @11
    va
    cvv
    crab
    #
    @12
    @2
    @19
    @11
    va
    cr
    crab
    #
    @22
    @2
    @18
    @11
    wi
    #
    va
    cr
    wral
    #
    @19
    @23
    wss
    @25
    @2
    @24
    va
    cr
    @17
    @10
    vc
    cn0
    @16
    @9
    vd
    cz
    @9
    @15
    simpl
    reximi
    reximi
    rgenw
    a1i
    @18
    @11
    va
    cr
    ss2rab
    sylibr
    cr
    cvv
    wss
    @23
    @22
    wss
    cr
    ssv
    @11
    va
    cr
    cvv
    rabss2
    ax-mp
    syl6ss
    @11
    va
    rabab
    syl6sseq
    eqsstrd
    @2
    @14
    @4
    wcel
    #
    @14
    @3
    cpellfund
    cfv
    #
    @5
    cexp
    co
    #
    wceq
    #
    va
    cz
    wrex
    #
    @2
    @1
    @14
    @27
    cN
    cexp
    co
    #
    wceq
    #
    @30
    @0
    @1
    simpr
    @2
    @13
    @27
    cN
    cexp
    @2
    @27
    @13
    @0
    @27
    @13
    wceq
    @1
    cA
    rmspecfund
    adantr
    eqcomd
    oveq1d
    @29
    @32
    va
    cN
    cz
    @5
    cN
    wceq
    @28
    @31
    @14
    @5
    cN
    @27
    cexp
    oveq2
    eqeq2d
    rspcev
    syl2anc
    @2
    @20
    @26
    @30
    wb
    @21
    va
    @14
    @3
    pellfund14b
    syl
    mpbird
    sseldd
end
