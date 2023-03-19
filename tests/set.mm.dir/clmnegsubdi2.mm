include "cclm.mm"
include "wcel.mm"
include "w3a.mm"
include "c1.mm"
include "cneg.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "wceq.mm"
include "simp1.mm"
include "eqid.mm"
include "clmneg1.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "wa.mm"
include "simpl.mm"
include "adantr.mm"
include "simpr.mm"
include "clmvscl.mm"
include "syl3anc.mm"
include "3adant2.mm"
include "clmvsdi.mm"
include "syl13anc.mm"
include "clmnegneg.mm"
include "oveq2d.mm"
include "cabl.mm"
include "clmabl.mm"
include "3adant3.mm"
include "simp3.mm"
include "ablcom.mm"
include "3eqtrd.mm"

theorem clmnegsubdi2
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cV: class V
  let cW: class W
  assume clmpm1dir.v: |- V = ( Base ` W )
  assume clmpm1dir.s: |- .x. = ( .s ` W )
  assume clmpm1dir.a: |- .+ = ( +g ` W )


  assert |- ( ( W e. CMod /\ A e. V /\ B e. V ) -> ( -u 1 .x. ( A .+ ( -u 1 .x. B ) ) ) = ( B .+ ( -u 1 .x. A ) ) )

  proof
    cW
    cclm
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    w3a
    #
    c1
    cneg
    #
    cA
    @4
    cB
    c.x
    co
    #
    c.pl
    co
    c.x
    co
    #
    @4
    cA
    c.x
    co
    #
    @4
    @5
    c.x
    co
    #
    c.pl
    co
    #
    @7
    cB
    c.pl
    co
    #
    cB
    @7
    c.pl
    co
    #
    @3
    @0
    @4
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @1
    @5
    cV
    wcel
    #
    @6
    @9
    wceq
    @0
    @1
    @2
    simp1
    @0
    @1
    @14
    @2
    @12
    @13
    cW
    @12
    eqid
    #
    @13
    eqid
    #
    clmneg1
    #
    3ad2ant1
    @0
    @1
    @2
    simp2
    @0
    @2
    @15
    @1
    @0
    @2
    wa
    @0
    @14
    @2
    @15
    @0
    @2
    simpl
    @0
    @14
    @2
    @18
    adantr
    @0
    @2
    simpr
    @4
    c.x
    @12
    @13
    cV
    cW
    cB
    clmpm1dir.v
    @16
    clmpm1dir.s
    @17
    clmvscl
    syl3anc
    3adant2
    @4
    c.pl
    c.x
    @12
    @13
    cV
    cW
    cA
    @5
    clmpm1dir.v
    @16
    clmpm1dir.s
    @17
    clmpm1dir.a
    clmvsdi
    syl13anc
    @3
    @8
    cB
    @7
    c.pl
    @0
    @2
    @8
    cB
    wceq
    @1
    cB
    c.pl
    c.x
    cV
    cW
    clmpm1dir.v
    clmpm1dir.s
    clmpm1dir.a
    clmnegneg
    3adant2
    oveq2d
    @3
    cW
    cabl
    wcel
    #
    @7
    cV
    wcel
    #
    @2
    @10
    @11
    wceq
    @0
    @1
    @19
    @2
    cW
    clmabl
    3ad2ant1
    @0
    @1
    @20
    @2
    @0
    @1
    wa
    @0
    @14
    @1
    @20
    @0
    @1
    simpl
    @0
    @14
    @1
    @18
    adantr
    @0
    @1
    simpr
    @4
    c.x
    @12
    @13
    cV
    cW
    cA
    clmpm1dir.v
    @16
    clmpm1dir.s
    @17
    clmvscl
    syl3anc
    3adant3
    @0
    @1
    @2
    simp3
    cV
    c.pl
    cW
    @7
    cB
    clmpm1dir.v
    clmpm1dir.a
    ablcom
    syl3anc
    3eqtrd
end
