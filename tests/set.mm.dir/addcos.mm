include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "ccos.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cmin.mm"
include "cmul.mm"
include "wceq.mm"
include "coscl.mm"
include "addcom.mm"
include "syl2an.mm"
include "halfaddsub.mm"
include "simprd.mm"
include "fveq2d.mm"
include "simpld.mm"
include "oveq12d.mm"
include "csin.mm"
include "halfaddsubcl.mm"
include "mulcl.mm"
include "syl.mm"
include "sincl.mm"
include "ppncand.mm"
include "cossub.mm"
include "cosadd.mm"
include "2timesd.mm"
include "3eqtr4d.mm"
include "3eqtr2d.mm"

theorem addcos
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( cos ` A ) + ( cos ` B ) ) = ( 2 x. ( ( cos ` ( ( A + B ) / 2 ) ) x. ( cos ` ( ( A - B ) / 2 ) ) ) ) )

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
    ccos
    cfv
    #
    cB
    ccos
    cfv
    #
    caddc
    co
    #
    @4
    @3
    caddc
    co
    #
    cA
    cB
    caddc
    co
    c2
    cdiv
    co
    #
    cA
    cB
    cmin
    co
    c2
    cdiv
    co
    #
    cmin
    co
    #
    ccos
    cfv
    #
    @7
    @8
    caddc
    co
    #
    ccos
    cfv
    #
    caddc
    co
    #
    c2
    @7
    ccos
    cfv
    #
    @8
    ccos
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    @0
    @3
    cc
    wcel
    @4
    cc
    wcel
    @5
    @6
    wceq
    @1
    cA
    coscl
    cB
    coscl
    @3
    @4
    addcom
    syl2an
    @2
    @10
    @4
    @12
    @3
    caddc
    @2
    @9
    cB
    ccos
    @2
    @11
    cA
    wceq
    #
    @9
    cB
    wceq
    #
    cA
    cB
    halfaddsub
    #
    simprd
    fveq2d
    @2
    @11
    cA
    ccos
    @2
    @18
    @19
    @20
    simpld
    fveq2d
    oveq12d
    @2
    @16
    @7
    csin
    cfv
    #
    @8
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @16
    @23
    cmin
    co
    #
    caddc
    co
    #
    @16
    @16
    caddc
    co
    @13
    @17
    @2
    @16
    @23
    @16
    @2
    @7
    cc
    wcel
    #
    @8
    cc
    wcel
    #
    wa
    #
    @16
    cc
    wcel
    #
    cA
    cB
    halfaddsubcl
    #
    @27
    @14
    cc
    wcel
    @15
    cc
    wcel
    @30
    @28
    @7
    coscl
    @8
    coscl
    @14
    @15
    mulcl
    syl2an
    syl
    #
    @2
    @29
    @23
    cc
    wcel
    #
    @31
    @27
    @21
    cc
    wcel
    @22
    cc
    wcel
    @33
    @28
    @7
    sincl
    @8
    sincl
    @21
    @22
    mulcl
    syl2an
    syl
    @32
    ppncand
    @2
    @29
    @13
    @26
    wceq
    @31
    @29
    @10
    @24
    @12
    @25
    caddc
    @7
    @8
    cossub
    @7
    @8
    cosadd
    oveq12d
    syl
    @2
    @16
    @32
    2timesd
    3eqtr4d
    3eqtr2d
end
