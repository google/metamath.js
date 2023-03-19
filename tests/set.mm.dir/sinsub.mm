include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "csin.mm"
include "cfv.mm"
include "ccos.mm"
include "cmul.mm"
include "cmin.mm"
include "wceq.mm"
include "negcl.mm"
include "sinadd.mm"
include "sylan2.mm"
include "negsub.mm"
include "fveq2d.mm"
include "cosneg.mm"
include "adantl.mm"
include "oveq2d.mm"
include "sinneg.mm"
include "coscl.mm"
include "sincl.mm"
include "mulneg2.mm"
include "syl2an.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "mulcl.mm"
include "negsubd.mm"
include "3eqtr3d.mm"

theorem sinsub
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( sin ` ( A - B ) ) = ( ( ( sin ` A ) x. ( cos ` B ) ) - ( ( cos ` A ) x. ( sin ` B ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    cneg
    #
    caddc
    co
    #
    csin
    cfv
    #
    cA
    csin
    cfv
    #
    @3
    ccos
    cfv
    #
    cmul
    co
    #
    cA
    ccos
    cfv
    #
    @3
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cA
    cB
    cmin
    co
    #
    csin
    cfv
    @6
    cB
    ccos
    cfv
    #
    cmul
    co
    #
    @9
    cB
    csin
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    @1
    @0
    @3
    cc
    wcel
    @5
    @12
    wceq
    cB
    negcl
    cA
    @3
    sinadd
    sylan2
    @2
    @4
    @13
    csin
    cA
    cB
    negsub
    fveq2d
    @2
    @12
    @15
    @17
    cneg
    #
    caddc
    co
    @18
    @2
    @8
    @15
    @11
    @19
    caddc
    @2
    @7
    @14
    @6
    cmul
    @1
    @7
    @14
    wceq
    @0
    cB
    cosneg
    adantl
    oveq2d
    @2
    @11
    @9
    @16
    cneg
    #
    cmul
    co
    #
    @19
    @2
    @10
    @20
    @9
    cmul
    @1
    @10
    @20
    wceq
    @0
    cB
    sinneg
    adantl
    oveq2d
    @0
    @9
    cc
    wcel
    #
    @16
    cc
    wcel
    #
    @21
    @19
    wceq
    @1
    cA
    coscl
    #
    cB
    sincl
    #
    @9
    @16
    mulneg2
    syl2an
    eqtrd
    oveq12d
    @2
    @15
    @17
    @0
    @6
    cc
    wcel
    @14
    cc
    wcel
    @15
    cc
    wcel
    @1
    cA
    sincl
    cB
    coscl
    @6
    @14
    mulcl
    syl2an
    @0
    @22
    @23
    @17
    cc
    wcel
    @1
    @24
    @25
    @9
    @16
    mulcl
    syl2an
    negsubd
    eqtrd
    3eqtr3d
end
