include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "crmy.mm"
include "cmul.mm"
include "cmin.mm"
include "peano2z.mm"
include "frmy.mm"
include "fovcl.mm"
include "sylan2.mm"
include "zcnd.mm"
include "cc.mm"
include "2cn.mm"
include "eluzelcn.mm"
include "adantr.mm"
include "mulcld.mm"
include "mulcl.mm"
include "sylancr.mm"
include "peano2zm.mm"
include "subcld.mm"
include "crmx.mm"
include "rmyp1.mm"
include "rmym1.mm"
include "oveq12d.mm"
include "cn0.mm"
include "frmx.mm"
include "nn0cnd.mm"
include "ppncand.mm"
include "npcand.mm"
include "2timesd.mm"
include "eqtr2d.mm"
include "3eqtrd.mm"
include "addcan2ad.mm"

theorem rmyluc
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY ( N + 1 ) ) = ( ( 2 x. ( ( A rmY N ) x. A ) ) - ( A rmY ( N - 1 ) ) ) )

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
    cN
    c1
    caddc
    co
    #
    crmy
    co
    #
    c2
    cA
    cN
    crmy
    co
    #
    cA
    cmul
    co
    #
    cmul
    co
    #
    cA
    cN
    c1
    cmin
    co
    #
    crmy
    co
    #
    cmin
    co
    #
    @10
    @3
    @5
    @2
    @1
    @4
    cz
    wcel
    @5
    cz
    wcel
    cN
    peano2z
    cA
    @4
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    sylan2
    zcnd
    @3
    @8
    @10
    @3
    c2
    cc
    wcel
    @7
    cc
    wcel
    @8
    cc
    wcel
    2cn
    @3
    @6
    cA
    @3
    @6
    cA
    cN
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    zcnd
    @1
    cA
    cc
    wcel
    @2
    c2
    cA
    eluzelcn
    adantr
    mulcld
    #
    c2
    @7
    mulcl
    sylancr
    #
    @3
    @10
    @2
    @1
    @9
    cz
    wcel
    @10
    cz
    wcel
    cN
    peano2zm
    cA
    @9
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    sylan2
    zcnd
    #
    subcld
    @14
    @3
    @5
    @10
    caddc
    co
    @7
    cA
    cN
    crmx
    co
    #
    caddc
    co
    #
    @7
    @15
    cmin
    co
    #
    caddc
    co
    @7
    @7
    caddc
    co
    #
    @11
    @10
    caddc
    co
    #
    @3
    @5
    @16
    @10
    @17
    caddc
    cA
    cN
    rmyp1
    cA
    cN
    rmym1
    oveq12d
    @3
    @7
    @15
    @7
    @12
    @3
    @15
    cA
    cN
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    nn0cnd
    @12
    ppncand
    @3
    @19
    @8
    @18
    @3
    @8
    @10
    @13
    @14
    npcand
    @3
    @7
    @12
    2timesd
    eqtr2d
    3eqtrd
    addcan2ad
end
