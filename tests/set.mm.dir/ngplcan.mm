include "cngp.mm"
include "wcel.mm"
include "cabl.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "simplr.mm"
include "simpr3.mm"
include "simpr1.mm"
include "ablcom.mm"
include "syl3anc.mm"
include "simpr2.mm"
include "oveq12d.mm"
include "ngprcan.mm"
include "adantlr.mm"
include "eqtrd.mm"

theorem ngplcan
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cG: class G
  let cX: class X
  assume ngprcan.x: |- X = ( Base ` G )
  assume ngprcan.p: |- .+ = ( +g ` G )
  assume ngprcan.d: |- D = ( dist ` G )


  assert |- ( ( ( G e. NrmGrp /\ G e. Abel ) /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( C .+ A ) D ( C .+ B ) ) = ( A D B ) )

  proof
    cG
    cngp
    wcel
    #
    cG
    cabl
    wcel
    #
    wa
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    wa
    #
    cC
    cA
    c.pl
    co
    #
    cC
    cB
    c.pl
    co
    #
    cD
    co
    cA
    cC
    c.pl
    co
    #
    cB
    cC
    c.pl
    co
    #
    cD
    co
    #
    cA
    cB
    cD
    co
    #
    @7
    @8
    @10
    @9
    @11
    cD
    @7
    @1
    @5
    @3
    @8
    @10
    wceq
    @0
    @1
    @6
    simplr
    #
    @2
    @3
    @4
    @5
    simpr3
    #
    @2
    @3
    @4
    @5
    simpr1
    cX
    c.pl
    cG
    cC
    cA
    ngprcan.x
    ngprcan.p
    ablcom
    syl3anc
    @7
    @1
    @5
    @4
    @9
    @11
    wceq
    @14
    @15
    @2
    @3
    @4
    @5
    simpr2
    cX
    c.pl
    cG
    cC
    cB
    ngprcan.x
    ngprcan.p
    ablcom
    syl3anc
    oveq12d
    @0
    @6
    @12
    @13
    wceq
    @1
    cA
    cB
    cC
    cD
    c.pl
    cG
    cX
    ngprcan.x
    ngprcan.p
    ngprcan.d
    ngprcan
    adantlr
    eqtrd
end
