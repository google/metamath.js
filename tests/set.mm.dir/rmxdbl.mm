include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "crmx.mm"
include "caddc.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "crmy.mm"
include "cc.mm"
include "zcn.mm"
include "adantl.mm"
include "2timesd.mm"
include "oveq2d.mm"
include "wceq.mm"
include "rmxadd.mm"
include "3anidm23.mm"
include "cn0.mm"
include "frmx.mm"
include "fovcl.mm"
include "nn0cnd.mm"
include "sqcld.mm"
include "cn.mm"
include "csquarenn.mm"
include "rmspecnonsq.mm"
include "eldifad.mm"
include "nncnd.mm"
include "adantr.mm"
include "frmy.mm"
include "zcnd.mm"
include "mulcld.mm"
include "pnncand.mm"
include "eqcomd.mm"
include "rmxynorm.mm"
include "oveq12d.mm"
include "sqvald.mm"
include "3eqtr3rd.mm"
include "3eqtrd.mm"

theorem rmxdbl
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmX ( 2 x. N ) ) = ( ( 2 x. ( ( A rmX N ) ^ 2 ) ) - 1 ) )

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
    crmx
    co
    cA
    cN
    cN
    caddc
    co
    #
    crmx
    co
    #
    cA
    cN
    crmx
    co
    #
    @7
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
    @10
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c2
    @7
    c2
    cexp
    co
    #
    cmul
    co
    #
    c1
    cmin
    co
    #
    @3
    @4
    @5
    cA
    crmx
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
    @13
    wceq
    cA
    cN
    cN
    rmxadd
    3anidm23
    @3
    @14
    @14
    caddc
    co
    #
    @14
    @9
    @10
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cmin
    co
    @14
    @19
    caddc
    co
    @16
    @13
    @3
    @14
    @14
    @19
    @3
    @7
    @3
    @7
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
    sqcld
    #
    @22
    @3
    @9
    @18
    @1
    @9
    cc
    wcel
    @2
    @1
    @9
    @1
    @9
    cn
    csquarenn
    cA
    rmspecnonsq
    eldifad
    nncnd
    adantr
    @3
    @10
    @3
    @10
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
    sqcld
    mulcld
    pnncand
    @3
    @17
    @15
    @20
    c1
    cmin
    @3
    @15
    @17
    @3
    @14
    @22
    2timesd
    eqcomd
    cA
    cN
    rmxynorm
    oveq12d
    @3
    @14
    @8
    @19
    @12
    caddc
    @3
    @7
    @21
    sqvald
    @3
    @18
    @11
    @9
    cmul
    @3
    @10
    @23
    sqvald
    oveq2d
    oveq12d
    3eqtr3rd
    3eqtrd
end
