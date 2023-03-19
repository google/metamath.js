include "cclm.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "csg.mm"
include "cfv.mm"
include "cminusg.mm"
include "c1.mm"
include "cneg.mm"
include "csca.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "clmsubdir.mm"
include "wceq.mm"
include "clmvscl.mm"
include "syl3anc.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "clmvneg1.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "3eqtrd.mm"

theorem clmpm1dir
  let cA: class A
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let c.x: class .x.
  let cK: class K
  let cV: class V
  let cW: class W
  assume clmpm1dir.v: |- V = ( Base ` W )
  assume clmpm1dir.s: |- .x. = ( .s ` W )
  assume clmpm1dir.a: |- .+ = ( +g ` W )
  assume clmpm1dir.k: |- K = ( Base ` ( Scalar ` W ) )


  assert |- ( ( W e. CMod /\ ( A e. K /\ B e. K /\ C e. V ) ) -> ( ( A - B ) .x. C ) = ( ( A .x. C ) .+ ( -u 1 .x. ( B .x. C ) ) ) )

  proof
    cW
    cclm
    wcel
    #
    cA
    cK
    wcel
    #
    cB
    cK
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
    cA
    cB
    cmin
    co
    cC
    c.x
    co
    cA
    cC
    c.x
    co
    #
    cB
    cC
    c.x
    co
    #
    cW
    csg
    cfv
    #
    co
    #
    @6
    @7
    cW
    cminusg
    cfv
    #
    cfv
    #
    c.pl
    co
    #
    @6
    c1
    cneg
    @7
    c.x
    co
    #
    c.pl
    co
    @5
    cA
    cB
    c.x
    cW
    csca
    cfv
    #
    cK
    @8
    cV
    cW
    cC
    clmpm1dir.v
    clmpm1dir.s
    @14
    eqid
    #
    clmpm1dir.k
    @8
    eqid
    #
    @0
    @4
    simpl
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    clmsubdir
    @5
    @6
    cV
    wcel
    #
    @7
    cV
    wcel
    #
    @9
    @12
    wceq
    @5
    @0
    @1
    @3
    @21
    @17
    @18
    @20
    cA
    c.x
    @14
    cK
    cV
    cW
    cC
    clmpm1dir.v
    @15
    clmpm1dir.s
    clmpm1dir.k
    clmvscl
    syl3anc
    @5
    @0
    @2
    @3
    @22
    @17
    @19
    @20
    cB
    c.x
    @14
    cK
    cV
    cW
    cC
    clmpm1dir.v
    @15
    clmpm1dir.s
    clmpm1dir.k
    clmvscl
    syl3anc
    #
    cV
    c.pl
    cW
    @10
    @8
    @6
    @7
    clmpm1dir.v
    clmpm1dir.a
    @10
    eqid
    #
    @16
    grpsubval
    syl2anc
    @5
    @11
    @13
    @6
    c.pl
    @5
    @0
    @22
    @11
    @13
    wceq
    @17
    @23
    @0
    @22
    wa
    @13
    @11
    c.x
    @14
    @10
    cV
    cW
    @7
    clmpm1dir.v
    @24
    @15
    clmpm1dir.s
    clmvneg1
    eqcomd
    syl2anc
    oveq2d
    3eqtrd
end
