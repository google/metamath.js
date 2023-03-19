include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "crmx.mm"
include "cmul.mm"
include "cexp.mm"
include "cmin.mm"
include "crmy.mm"
include "wceq.mm"
include "neg1z.mm"
include "rmxadd.mm"
include "mp3an3.mm"
include "1z.mm"
include "rmxneg.mm"
include "mpan2.mm"
include "rmx1.mm"
include "eqtrd.mm"
include "adantr.mm"
include "oveq2d.mm"
include "cn0.mm"
include "frmx.mm"
include "fovcl.mm"
include "nn0cnd.mm"
include "cc.mm"
include "eluzelcn.mm"
include "mulcomd.mm"
include "rmyneg.mm"
include "rmy1.mm"
include "negeqd.mm"
include "frmy.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "mulneg2.mm"
include "sylancl.mm"
include "mulid1d.mm"
include "cn.mm"
include "csquarenn.mm"
include "rmspecnonsq.mm"
include "eldifad.mm"
include "nncnd.mm"
include "mulneg2d.mm"
include "oveq12d.mm"
include "zcn.mm"
include "adantl.mm"
include "negsub.mm"
include "mulcld.mm"
include "negsubd.mm"
include "3eqtr3d.mm"

theorem rmxm1
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmX ( N - 1 ) ) = ( ( A x. ( A rmX N ) ) - ( ( ( A ^ 2 ) - 1 ) x. ( A rmY N ) ) ) )

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
    cneg
    #
    caddc
    co
    #
    crmx
    co
    #
    cA
    cA
    cN
    crmx
    co
    #
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
    cneg
    #
    caddc
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
    @8
    @11
    cmin
    co
    @3
    @6
    @7
    cA
    @4
    crmx
    co
    #
    cmul
    co
    #
    @9
    @10
    cA
    @4
    crmy
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @13
    @1
    @2
    @4
    cz
    wcel
    @6
    @20
    wceq
    neg1z
    cA
    cN
    @4
    rmxadd
    mp3an3
    @3
    @16
    @8
    @19
    @12
    caddc
    @3
    @16
    @7
    cA
    cmul
    co
    @8
    @3
    @15
    cA
    @7
    cmul
    @1
    @15
    cA
    wceq
    @2
    @1
    @15
    cA
    c1
    crmx
    co
    #
    cA
    @1
    c1
    cz
    wcel
    #
    @15
    @21
    wceq
    1z
    cA
    c1
    rmxneg
    mpan2
    cA
    rmx1
    eqtrd
    adantr
    oveq2d
    @3
    @7
    cA
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
    @1
    cA
    cc
    wcel
    @2
    c2
    cA
    eluzelcn
    adantr
    #
    mulcomd
    eqtrd
    @3
    @19
    @9
    @10
    cneg
    #
    cmul
    co
    @12
    @3
    @18
    @25
    @9
    cmul
    @3
    @18
    @10
    @4
    cmul
    co
    #
    @25
    @1
    @18
    @26
    wceq
    @2
    @1
    @17
    @4
    @10
    cmul
    @1
    @17
    cA
    c1
    crmy
    co
    #
    cneg
    #
    @4
    @1
    @22
    @17
    @28
    wceq
    1z
    cA
    c1
    rmyneg
    mpan2
    @1
    @27
    c1
    cA
    rmy1
    negeqd
    eqtrd
    oveq2d
    adantr
    @3
    @26
    @10
    c1
    cmul
    co
    #
    cneg
    #
    @25
    @3
    @10
    cc
    wcel
    c1
    cc
    wcel
    #
    @26
    @30
    wceq
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
    ax-1cn
    @10
    c1
    mulneg2
    sylancl
    @3
    @29
    @10
    @3
    @10
    @32
    mulid1d
    negeqd
    eqtrd
    eqtrd
    oveq2d
    @3
    @9
    @10
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
    #
    @32
    mulneg2d
    eqtrd
    oveq12d
    eqtrd
    @3
    @5
    @14
    cA
    crmx
    @3
    cN
    cc
    wcel
    #
    @31
    @5
    @14
    wceq
    @2
    @34
    @1
    cN
    zcn
    adantl
    ax-1cn
    cN
    c1
    negsub
    sylancl
    oveq2d
    @3
    @8
    @11
    @3
    cA
    @7
    @24
    @23
    mulcld
    @3
    @9
    @10
    @33
    @32
    mulcld
    negsubd
    3eqtr3d
end
