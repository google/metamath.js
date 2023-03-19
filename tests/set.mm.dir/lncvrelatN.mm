include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wne.mm"
include "cjn.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "isline2.mm"
include "syl.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simplrl.mm"
include "atbase.mm"
include "simplrr.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "pmap11.mm"
include "breq2.mm"
include "biimpd.mm"
include "adantr.mm"
include "simpll3.mm"
include "3jca.mm"
include "simplr.mm"
include "simpr.mm"
include "cvrat2.mm"
include "syl112anc.mm"
include "ex.mm"
include "syl9r.mm"
include "sylbid.mm"
include "expimpd.mm"
include "rexlimdvva.mm"
include "imp32.mm"

theorem lncvrelatN
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cK: class K
  let cM: class M
  let cN: class N
  let cX: class X
  let vq: setvar q
  let vr: setvar r
  assume lncvrelat.b: |- B = ( Base ` K )
  assume lncvrelat.c: |- C = ( <o ` K )
  assume lncvrelat.a: |- A = ( Atoms ` K )
  assume lncvrelat.n: |- N = ( Lines ` K )
  assume lncvrelat.m: |- M = ( pmap ` K )


  assert |- ( ( ( K e. HL /\ X e. B /\ P e. B ) /\ ( ( M ` X ) e. N /\ P C X ) ) -> P e. A )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cP
    cB
    wcel
    #
    w3a
    #
    cX
    cM
    cfv
    #
    cN
    wcel
    #
    cP
    cX
    cC
    wbr
    #
    cP
    cA
    wcel
    #
    @3
    @5
    vq
    cv
    #
    vr
    cv
    #
    wne
    #
    @4
    @8
    @9
    cK
    cjn
    cfv
    #
    co
    #
    cM
    cfv
    wceq
    #
    wa
    #
    vr
    cA
    wrex
    vq
    cA
    wrex
    #
    @6
    @7
    wi
    #
    @3
    cK
    clat
    wcel
    #
    @5
    @15
    wb
    @0
    @1
    @17
    @2
    cK
    hllat
    #
    3ad2ant1
    cA
    @11
    cK
    cM
    cN
    @4
    vr
    vq
    @11
    eqid
    #
    lncvrelat.a
    lncvrelat.n
    lncvrelat.m
    isline2
    syl
    @3
    @14
    @16
    vq
    vr
    cA
    cA
    @3
    @8
    cA
    wcel
    #
    @9
    cA
    wcel
    #
    wa
    #
    wa
    #
    @10
    @13
    @16
    @23
    @10
    wa
    #
    @13
    cX
    @12
    wceq
    #
    @16
    @24
    @0
    @1
    @12
    cB
    wcel
    #
    @13
    @25
    wb
    @0
    @1
    @2
    @22
    @10
    simpll1
    #
    @0
    @1
    @2
    @22
    @10
    simpll2
    @24
    @17
    @8
    cB
    wcel
    #
    @9
    cB
    wcel
    #
    @26
    @24
    @0
    @17
    @27
    @18
    syl
    @24
    @20
    @28
    @3
    @20
    @21
    @10
    simplrl
    #
    cA
    cB
    @8
    cK
    lncvrelat.b
    lncvrelat.a
    atbase
    syl
    @24
    @21
    @29
    @3
    @20
    @21
    @10
    simplrr
    #
    cA
    cB
    @9
    cK
    lncvrelat.b
    lncvrelat.a
    atbase
    syl
    cB
    @11
    cK
    @8
    @9
    lncvrelat.b
    @19
    latjcl
    syl3anc
    cB
    cK
    cM
    cX
    @12
    lncvrelat.b
    lncvrelat.m
    pmap11
    syl3anc
    @25
    @6
    cP
    @12
    cC
    wbr
    #
    @24
    @7
    @25
    @6
    @32
    cX
    @12
    cP
    cC
    breq2
    biimpd
    @24
    @32
    @7
    @24
    @32
    wa
    @0
    @2
    @20
    @21
    w3a
    #
    @10
    @32
    @7
    @24
    @0
    @32
    @27
    adantr
    @24
    @33
    @32
    @24
    @2
    @20
    @21
    @0
    @1
    @2
    @22
    @10
    simpll3
    @30
    @31
    3jca
    adantr
    @23
    @10
    @32
    simplr
    @24
    @32
    simpr
    cA
    cB
    cC
    @8
    @9
    @11
    cK
    cP
    lncvrelat.b
    @19
    lncvrelat.c
    lncvrelat.a
    cvrat2
    syl112anc
    ex
    syl9r
    sylbid
    expimpd
    rexlimdvva
    sylbid
    imp32
end
