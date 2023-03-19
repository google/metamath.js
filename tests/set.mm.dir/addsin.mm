include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "csin.mm"
include "cfv.mm"
include "cmin.mm"
include "ccos.mm"
include "cmul.mm"
include "addcl.mm"
include "halfcld.mm"
include "sincld.mm"
include "subcl.mm"
include "coscld.mm"
include "mulcld.mm"
include "2timesd.mm"
include "wceq.mm"
include "sinadd.mm"
include "syl2anc.mm"
include "sinsub.mm"
include "oveq12d.mm"
include "ppncand.mm"
include "eqtrd.mm"
include "halfaddsub.mm"
include "simpld.mm"
include "fveq2d.mm"
include "simprd.mm"
include "3eqtr2rd.mm"

theorem addsin
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( sin ` A ) + ( sin ` B ) ) = ( 2 x. ( ( sin ` ( ( A + B ) / 2 ) ) x. ( cos ` ( ( A - B ) / 2 ) ) ) ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    wa
    #
    c2
    cA
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cA
    cB
    cmin
    co
    #
    c2
    cdiv
    co
    #
    ccos
    cfv
    #
    cmul
    co
    #
    cmul
    co
    @7
    @7
    caddc
    co
    #
    @2
    @5
    caddc
    co
    #
    csin
    cfv
    #
    @2
    @5
    cmin
    co
    #
    csin
    cfv
    #
    caddc
    co
    #
    cA
    csin
    cfv
    #
    cB
    csin
    cfv
    #
    caddc
    co
    @0
    @7
    @0
    @3
    @6
    @0
    @2
    @0
    @1
    cA
    cB
    addcl
    halfcld
    #
    sincld
    @0
    @5
    @0
    @4
    cA
    cB
    subcl
    halfcld
    #
    coscld
    mulcld
    #
    2timesd
    @0
    @13
    @7
    @2
    ccos
    cfv
    #
    @5
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @7
    @21
    cmin
    co
    #
    caddc
    co
    @8
    @0
    @10
    @22
    @12
    @23
    caddc
    @0
    @2
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @10
    @22
    wceq
    @16
    @17
    @2
    @5
    sinadd
    syl2anc
    @0
    @24
    @25
    @12
    @23
    wceq
    @16
    @17
    @2
    @5
    sinsub
    syl2anc
    oveq12d
    @0
    @7
    @21
    @7
    @18
    @0
    @19
    @20
    @0
    @2
    @16
    coscld
    @0
    @5
    @17
    sincld
    mulcld
    @18
    ppncand
    eqtrd
    @0
    @10
    @14
    @12
    @15
    caddc
    @0
    @9
    cA
    csin
    @0
    @9
    cA
    wceq
    #
    @11
    cB
    wceq
    #
    cA
    cB
    halfaddsub
    #
    simpld
    fveq2d
    @0
    @11
    cB
    csin
    @0
    @26
    @27
    @28
    simprd
    fveq2d
    oveq12d
    3eqtr2rd
end
