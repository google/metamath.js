include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "crmy.mm"
include "cneg.mm"
include "caddc.mm"
include "crmx.mm"
include "cmul.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "adantl.mm"
include "ax-1cn.mm"
include "negsub.mm"
include "sylancl.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "neg1z.mm"
include "rmyadd.mm"
include "mp3an3.mm"
include "1z.mm"
include "rmxneg.mm"
include "mpan2.mm"
include "rmx1.mm"
include "eqtrd.mm"
include "adantr.mm"
include "rmyneg.mm"
include "rmy1.mm"
include "negeqd.mm"
include "cn0.mm"
include "frmx.mm"
include "fovcl.mm"
include "nn0cnd.mm"
include "neg1cn.mm"
include "mulcom.mm"
include "mulm1d.mm"
include "3eqtrd.mm"
include "oveq12d.mm"
include "frmy.mm"
include "zcnd.mm"
include "eluzelcn.mm"
include "mulcld.mm"
include "negsubd.mm"

theorem rmym1
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY ( N - 1 ) ) = ( ( ( A rmY N ) x. A ) - ( A rmX N ) ) )

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
    cmin
    co
    #
    crmy
    co
    cA
    cN
    c1
    cneg
    #
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
    @5
    crmx
    co
    #
    cmul
    co
    #
    cA
    cN
    crmx
    co
    #
    cA
    @5
    crmy
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @8
    cA
    cmul
    co
    #
    @11
    cmin
    co
    #
    @3
    @4
    @6
    cA
    crmy
    @3
    @6
    @4
    @3
    cN
    cc
    wcel
    #
    c1
    cc
    wcel
    @6
    @4
    wceq
    @2
    @17
    @1
    cN
    zcn
    adantl
    ax-1cn
    cN
    c1
    negsub
    sylancl
    eqcomd
    oveq2d
    @1
    @2
    @5
    cz
    wcel
    @7
    @14
    wceq
    neg1z
    cA
    cN
    @5
    rmyadd
    mp3an3
    @3
    @14
    @15
    @11
    cneg
    #
    caddc
    co
    @16
    @3
    @10
    @15
    @13
    @18
    caddc
    @3
    @9
    cA
    @8
    cmul
    @1
    @9
    cA
    wceq
    @2
    @1
    @9
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
    @9
    @19
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
    @13
    @11
    @5
    cmul
    co
    #
    @5
    @11
    cmul
    co
    #
    @18
    @3
    @12
    @5
    @11
    cmul
    @1
    @12
    @5
    wceq
    @2
    @1
    @12
    cA
    c1
    crmy
    co
    #
    cneg
    #
    @5
    @1
    @20
    @12
    @24
    wceq
    1z
    cA
    c1
    rmyneg
    mpan2
    @1
    @23
    c1
    cA
    rmy1
    negeqd
    eqtrd
    adantr
    oveq2d
    @3
    @11
    cc
    wcel
    @5
    cc
    wcel
    @21
    @22
    wceq
    @3
    @11
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
    neg1cn
    @11
    @5
    mulcom
    sylancl
    @3
    @11
    @25
    mulm1d
    3eqtrd
    oveq12d
    @3
    @15
    @11
    @3
    @8
    cA
    @3
    @8
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
    @25
    negsubd
    eqtrd
    3eqtrd
end
