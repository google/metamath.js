include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "crmy.mm"
include "caddc.mm"
include "crmx.mm"
include "cc.mm"
include "zcn.mm"
include "adantl.mm"
include "2timesd.mm"
include "oveq2d.mm"
include "wceq.mm"
include "rmyadd.mm"
include "3anidm23.mm"
include "2cnd.mm"
include "cn0.mm"
include "frmx.mm"
include "fovcl.mm"
include "nn0cnd.mm"
include "frmy.mm"
include "zcnd.mm"
include "mulassd.mm"
include "mulcld.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "3eqtrrd.mm"
include "3eqtrd.mm"

theorem rmydbl
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY ( 2 x. N ) ) = ( ( 2 x. ( A rmX N ) ) x. ( A rmY N ) ) )

  proof
    cA
    c2
    cuz
    cfv
    #
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
    cN
    cmul
    co
    #
    crmy
    co
    cA
    cN
    cN
    caddc
    co
    #
    crmy
    co
    #
    cA
    cN
    crmy
    co
    #
    cA
    cN
    crmx
    co
    #
    cmul
    co
    #
    @8
    @7
    cmul
    co
    #
    caddc
    co
    #
    c2
    @8
    cmul
    co
    @7
    cmul
    co
    #
    @3
    @4
    @5
    cA
    crmy
    @3
    cN
    @2
    cN
    cc
    wcel
    @1
    cN
    zcn
    adantl
    2timesd
    oveq2d
    @1
    @2
    @6
    @11
    wceq
    cA
    cN
    cN
    rmyadd
    3anidm23
    @3
    @12
    c2
    @10
    cmul
    co
    @10
    @10
    caddc
    co
    @11
    @3
    c2
    @8
    @7
    @3
    2cnd
    @3
    @8
    cA
    cN
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    nn0cnd
    #
    @3
    @7
    cA
    cN
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    zcnd
    #
    mulassd
    @3
    @10
    @3
    @8
    @7
    @13
    @14
    mulcld
    2timesd
    @3
    @10
    @9
    @10
    caddc
    @3
    @8
    @7
    @13
    @14
    mulcomd
    oveq1d
    3eqtrrd
    3eqtrd
end
