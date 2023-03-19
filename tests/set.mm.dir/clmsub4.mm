include "cclm.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "wceq.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "simpl.mm"
include "eqid.mm"
include "clmneg1.mm"
include "adantr.mm"
include "adantl.mm"
include "simpr.mm"
include "clmvsdi.mm"
include "syl13anc.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "ccmn.mm"
include "cabl.mm"
include "clmabl.mm"
include "ablcmn.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "clmvscl.mm"
include "syl3anc.mm"
include "anim12dan.mm"
include "cmn4.mm"
include "eqtrd.mm"

theorem clmsub4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.x: class .x.
  let cV: class V
  let cW: class W
  assume clmpm1dir.v: |- V = ( Base ` W )
  assume clmpm1dir.s: |- .x. = ( .s ` W )
  assume clmpm1dir.a: |- .+ = ( +g ` W )


  assert |- ( ( W e. CMod /\ ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) -> ( ( A .+ B ) .+ ( -u 1 .x. ( C .+ D ) ) ) = ( ( A .+ ( -u 1 .x. C ) ) .+ ( B .+ ( -u 1 .x. D ) ) ) )

  proof
    cW
    cclm
    wcel
    #
    cA
    cV
    wcel
    cB
    cV
    wcel
    wa
    #
    cC
    cV
    wcel
    #
    cD
    cV
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cB
    c.pl
    co
    #
    c1
    cneg
    #
    cC
    cD
    c.pl
    co
    c.x
    co
    #
    c.pl
    co
    @6
    @7
    cC
    c.x
    co
    #
    @7
    cD
    c.x
    co
    #
    c.pl
    co
    #
    c.pl
    co
    #
    cA
    @9
    c.pl
    co
    cB
    @10
    c.pl
    co
    c.pl
    co
    #
    @5
    @8
    @11
    @6
    c.pl
    @0
    @4
    @8
    @11
    wceq
    #
    @1
    @0
    @4
    wa
    @0
    @7
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @2
    @3
    @14
    @0
    @4
    simpl
    @0
    @17
    @4
    @15
    @16
    cW
    @15
    eqid
    #
    @16
    eqid
    #
    clmneg1
    #
    adantr
    @4
    @2
    @0
    @2
    @3
    simpl
    adantl
    @4
    @3
    @0
    @2
    @3
    simpr
    adantl
    @7
    c.pl
    c.x
    @15
    @16
    cV
    cW
    cC
    cD
    clmpm1dir.v
    @18
    clmpm1dir.s
    @19
    clmpm1dir.a
    clmvsdi
    syl13anc
    3adant2
    oveq2d
    @5
    cW
    ccmn
    wcel
    #
    @1
    @9
    cV
    wcel
    #
    @10
    cV
    wcel
    #
    wa
    #
    @12
    @13
    wceq
    @0
    @1
    @21
    @4
    @0
    cW
    cabl
    wcel
    @21
    cW
    clmabl
    cW
    ablcmn
    syl
    3ad2ant1
    @0
    @1
    @4
    simp2
    @0
    @4
    @24
    @1
    @0
    @2
    @22
    @3
    @23
    @0
    @2
    wa
    @0
    @17
    @2
    @22
    @0
    @2
    simpl
    @0
    @17
    @2
    @20
    adantr
    @0
    @2
    simpr
    @7
    c.x
    @15
    @16
    cV
    cW
    cC
    clmpm1dir.v
    @18
    clmpm1dir.s
    @19
    clmvscl
    syl3anc
    @0
    @3
    wa
    @0
    @17
    @3
    @23
    @0
    @3
    simpl
    @0
    @17
    @3
    @20
    adantr
    @0
    @3
    simpr
    @7
    c.x
    @15
    @16
    cV
    cW
    cD
    clmpm1dir.v
    @18
    clmpm1dir.s
    @19
    clmvscl
    syl3anc
    anim12dan
    3adant2
    cV
    c.pl
    cW
    @10
    cA
    cB
    @9
    clmpm1dir.v
    clmpm1dir.a
    cmn4
    syl3anc
    eqtrd
end
