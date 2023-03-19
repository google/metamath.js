include "ccph.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "cstv.mm"
include "cmulr.mm"
include "cclm.mm"
include "wceq.mm"
include "cphclm.mm"
include "adantr.mm"
include "clmmul.mm"
include "syl.mm"
include "eqidd.mm"
include "clmcj.mm"
include "fveq1d.mm"
include "oveq123d.mm"
include "cc.mm"
include "wss.mm"
include "clmsscn.mm"
include "simpr1.mm"
include "sseldd.mm"
include "cjcld.mm"
include "cphipcl.mm"
include "3adant3r1.mm"
include "mulcomd.mm"
include "cphl.mm"
include "cphphl.mm"
include "3anrot.mm"
include "biimpi.mm"
include "eqid.mm"
include "ipassr.mm"
include "syl2an.mm"
include "3eqtr4rd.mm"

theorem cphassr
  let cA: class A
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cF: class F
  let c.xi: class .,
  let cK: class K
  let cV: class V
  let cW: class W
  assume cphipcj.h: |- ., = ( .i ` W )
  assume cphipcj.v: |- V = ( Base ` W )
  assume cphass.f: |- F = ( Scalar ` W )
  assume cphass.k: |- K = ( Base ` F )
  assume cphass.s: |- .x. = ( .s ` W )


  assert |- ( ( W e. CPreHil /\ ( A e. K /\ B e. V /\ C e. V ) ) -> ( B ., ( A .x. C ) ) = ( ( * ` A ) x. ( B ., C ) ) )

  proof
    cW
    ccph
    wcel
    #
    cA
    cK
    wcel
    #
    cB
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    w3a
    #
    wa
    #
    cB
    cC
    c.xi
    co
    #
    cA
    ccj
    cfv
    #
    cmul
    co
    @6
    cA
    cF
    cstv
    cfv
    #
    cfv
    #
    cF
    cmulr
    cfv
    #
    co
    #
    @7
    @6
    cmul
    co
    cB
    cA
    cC
    c.x
    co
    c.xi
    co
    #
    @5
    @6
    @6
    @7
    @9
    cmul
    @10
    @5
    cW
    cclm
    wcel
    #
    cmul
    @10
    wceq
    @0
    @13
    @4
    cW
    cphclm
    adantr
    #
    cF
    cW
    cphass.f
    clmmul
    syl
    @5
    @6
    eqidd
    @5
    cA
    ccj
    @8
    @5
    @13
    ccj
    @8
    wceq
    @14
    cF
    cW
    cphass.f
    clmcj
    syl
    fveq1d
    oveq123d
    @5
    @7
    @6
    @5
    cA
    @5
    cK
    cc
    cA
    @5
    @13
    cK
    cc
    wss
    @14
    cF
    cK
    cW
    cphass.f
    cphass.k
    clmsscn
    syl
    @0
    @1
    @2
    @3
    simpr1
    sseldd
    cjcld
    @0
    @2
    @3
    @6
    cc
    wcel
    @1
    cB
    cC
    c.xi
    cV
    cW
    cphipcj.v
    cphipcj.h
    cphipcl
    3adant3r1
    mulcomd
    @0
    cW
    cphl
    wcel
    @2
    @3
    @1
    w3a
    #
    @12
    @11
    wceq
    @4
    cW
    cphphl
    @4
    @15
    @1
    @2
    @3
    3anrot
    biimpi
    cB
    cC
    cA
    c.x
    @10
    cF
    c.xi
    @8
    cK
    cV
    cW
    cphass.f
    cphipcj.h
    cphipcj.v
    cphass.k
    cphass.s
    @10
    eqid
    @8
    eqid
    ipassr
    syl2an
    3eqtr4rd
end
