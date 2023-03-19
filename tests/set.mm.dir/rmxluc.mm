include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "crmx.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "wceq.mm"
include "cexp.mm"
include "crmy.mm"
include "cc.mm"
include "peano2zm.mm"
include "cn0.mm"
include "frmx.mm"
include "fovcl.mm"
include "nn0cnd.mm"
include "sylan2.mm"
include "peano2z.mm"
include "addcomd.mm"
include "rmxp1.mm"
include "rmxm1.mm"
include "oveq12d.mm"
include "eluzelcn.mm"
include "adantr.mm"
include "mulcld.mm"
include "cn.mm"
include "csquarenn.mm"
include "rmspecnonsq.mm"
include "eldifad.mm"
include "nncnd.mm"
include "frmy.mm"
include "zcnd.mm"
include "ppncand.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "2cnd.mm"
include "mulassd.mm"
include "2timesd.mm"
include "eqtr2d.mm"
include "3eqtrd.mm"
include "2cn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "subaddd.mm"
include "mpbird.mm"
include "eqcomd.mm"

theorem rmxluc
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmX ( N + 1 ) ) = ( ( ( 2 x. A ) x. ( A rmX N ) ) - ( A rmX ( N - 1 ) ) ) )

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
    c2
    cA
    cmul
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
    cA
    cN
    c1
    cmin
    co
    #
    crmx
    co
    #
    cmin
    co
    #
    cA
    cN
    c1
    caddc
    co
    #
    crmx
    co
    #
    @3
    @9
    @11
    wceq
    @8
    @11
    caddc
    co
    #
    @6
    wceq
    @3
    @12
    @11
    @8
    caddc
    co
    @5
    cA
    cmul
    co
    #
    cA
    c2
    cexp
    co
    c1
    cmin
    co
    #
    cA
    cN
    crmy
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    cA
    @5
    cmul
    co
    #
    @16
    cmin
    co
    #
    caddc
    co
    #
    @6
    @3
    @8
    @11
    @2
    @1
    @7
    cz
    wcel
    #
    @8
    cc
    wcel
    cN
    peano2zm
    @1
    @21
    wa
    @8
    cA
    @7
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    nn0cnd
    sylan2
    #
    @2
    @1
    @10
    cz
    wcel
    #
    @11
    cc
    wcel
    cN
    peano2z
    @1
    @23
    wa
    @11
    cA
    @10
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    nn0cnd
    sylan2
    #
    addcomd
    @3
    @11
    @17
    @8
    @19
    caddc
    cA
    cN
    rmxp1
    cA
    cN
    rmxm1
    oveq12d
    @3
    @20
    @13
    @18
    caddc
    co
    @18
    @18
    caddc
    co
    #
    @6
    @3
    @13
    @16
    @18
    @3
    @5
    cA
    @3
    @5
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
    @1
    cA
    cc
    wcel
    #
    @2
    c2
    cA
    eluzelcn
    adantr
    #
    mulcld
    @3
    @14
    @15
    @1
    @14
    cc
    wcel
    @2
    @1
    @14
    @1
    @14
    cn
    csquarenn
    cA
    rmspecnonsq
    eldifad
    nncnd
    adantr
    @3
    @15
    cA
    cN
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    zcnd
    mulcld
    @3
    cA
    @5
    @28
    @26
    mulcld
    #
    ppncand
    @3
    @13
    @18
    @18
    caddc
    @3
    @5
    cA
    @26
    @28
    mulcomd
    oveq1d
    @3
    @6
    c2
    @18
    cmul
    co
    @25
    @3
    c2
    cA
    @5
    @3
    2cnd
    @28
    @26
    mulassd
    @3
    @18
    @29
    2timesd
    eqtr2d
    3eqtrd
    3eqtrd
    @3
    @6
    @8
    @11
    @3
    @4
    @5
    @3
    c2
    cc
    wcel
    @27
    @4
    cc
    wcel
    2cn
    @28
    c2
    cA
    mulcl
    sylancr
    @26
    mulcld
    @22
    @24
    subaddd
    mpbird
    eqcomd
end
