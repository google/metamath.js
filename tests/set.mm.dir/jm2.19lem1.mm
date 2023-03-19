include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "crmx.mm"
include "co.mm"
include "cmul.mm"
include "crmy.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "cneg.mm"
include "caddc.mm"
include "wceq.mm"
include "cgcd.mm"
include "cn0.mm"
include "frmx.mm"
include "fovcl.mm"
include "nn0cnd.mm"
include "sqcld.mm"
include "cn.mm"
include "csquarenn.mm"
include "rmspecnonsq.mm"
include "eldifad.mm"
include "adantr.mm"
include "nncnd.mm"
include "frmy.mm"
include "zcnd.mm"
include "mulcld.mm"
include "negsubd.mm"
include "sqvald.mm"
include "oveq2d.mm"
include "mulneg1d.mm"
include "nnnegz.mm"
include "syl.mm"
include "mul12d.mm"
include "3eqtr3d.mm"
include "oveq12d.mm"
include "rmxynorm.mm"
include "wi.mm"
include "nn0zd.mm"
include "zmulcld.mm"
include "bezoutr1.mm"
include "syl22anc.mm"
include "mpd.mm"

theorem jm2.19lem1
  let cA: class A
  let cM: class M


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ ) -> ( ( A rmX M ) gcd ( A rmY M ) ) = 1 )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cM
    cz
    wcel
    #
    wa
    #
    cA
    cM
    crmx
    co
    #
    @4
    cmul
    co
    #
    cA
    cM
    crmy
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
    cneg
    #
    @6
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c1
    wceq
    #
    @4
    @6
    cgcd
    co
    c1
    wceq
    #
    @3
    @4
    c2
    cexp
    co
    #
    @7
    @6
    c2
    cexp
    co
    #
    cmul
    co
    #
    cneg
    #
    caddc
    co
    @14
    @16
    cmin
    co
    @11
    c1
    @3
    @14
    @16
    @3
    @4
    @3
    @4
    cA
    cM
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    #
    nn0cnd
    #
    sqcld
    @3
    @7
    @15
    @3
    @7
    @1
    @7
    cn
    wcel
    #
    @2
    @1
    @7
    cn
    csquarenn
    cA
    rmspecnonsq
    eldifad
    adantr
    #
    nncnd
    #
    @3
    @6
    @3
    @6
    cA
    cM
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    #
    zcnd
    #
    sqcld
    #
    mulcld
    negsubd
    @3
    @14
    @5
    @17
    @10
    caddc
    @3
    @4
    @19
    sqvald
    @3
    @8
    @15
    cmul
    co
    @8
    @6
    @6
    cmul
    co
    #
    cmul
    co
    @17
    @10
    @3
    @15
    @26
    @8
    cmul
    @3
    @6
    @24
    sqvald
    oveq2d
    @3
    @7
    @15
    @22
    @25
    mulneg1d
    @3
    @8
    @6
    @6
    @3
    @8
    @3
    @20
    @8
    cz
    wcel
    @21
    @7
    nnnegz
    syl
    #
    zcnd
    @24
    @24
    mul12d
    3eqtr3d
    oveq12d
    cA
    cM
    rmxynorm
    3eqtr3d
    @3
    @4
    cz
    wcel
    #
    @6
    cz
    wcel
    @28
    @9
    cz
    wcel
    @12
    @13
    wi
    @3
    @4
    @18
    nn0zd
    #
    @23
    @29
    @3
    @8
    @6
    @27
    @23
    zmulcld
    @4
    @6
    @4
    @9
    bezoutr1
    syl22anc
    mpd
end
