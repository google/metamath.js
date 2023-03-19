include "cc.mm"
include "wcel.mm"
include "csinh.mm"
include "cfv.mm"
include "ccosh.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "ce.mm"
include "cmul.mm"
include "cdiv.mm"
include "cneg.mm"
include "cmin.mm"
include "ci.mm"
include "csin.mm"
include "sinhval-named.mm"
include "sinhval.mm"
include "eqtrd.mm"
include "ccos.mm"
include "coshval-named.mm"
include "coshval.mm"
include "oveq12d.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "2cn.mm"
include "2ne0.mm"
include "wa.mm"
include "efcl.mm"
include "negcl.mm"
include "syl.mm"
include "addcld.mm"
include "subcld.mm"
include "divdir.mm"
include "syl3an1.mm"
include "syl3an2.mm"
include "3anidm12.mm"
include "mpanr12.mm"
include "2timesd.mm"
include "nppcand.mm"
include "addassd.mm"
include "3eqtr2rd.mm"
include "oveq1d.mm"
include "3eqtr2d.mm"
include "a1i.mm"
include "divcan3d.mm"

theorem sinhpcosh
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( A e. CC -> ( ( sinh ` A ) + ( cosh ` A ) ) = ( exp ` A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    csinh
    cfv
    #
    cA
    ccosh
    cfv
    #
    caddc
    co
    #
    c2
    cA
    ce
    cfv
    #
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @4
    @0
    @3
    @4
    cA
    cneg
    #
    ce
    cfv
    #
    cmin
    co
    #
    c2
    cdiv
    co
    #
    @4
    @8
    caddc
    co
    #
    c2
    cdiv
    co
    #
    caddc
    co
    #
    @9
    @11
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @6
    @0
    @1
    @10
    @2
    @12
    caddc
    @0
    @1
    ci
    cA
    cmul
    co
    #
    csin
    cfv
    ci
    cdiv
    co
    @10
    cA
    sinhval-named
    cA
    sinhval
    eqtrd
    @0
    @2
    @16
    ccos
    cfv
    @12
    cA
    coshval-named
    cA
    coshval
    eqtrd
    oveq12d
    @0
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    @15
    @13
    wceq
    #
    2cn
    2ne0
    @0
    @17
    @18
    wa
    #
    @19
    @0
    @0
    @11
    cc
    wcel
    #
    @20
    @19
    @0
    @4
    @8
    cA
    efcl
    #
    @0
    @7
    cc
    wcel
    @8
    cc
    wcel
    cA
    negcl
    @7
    efcl
    syl
    #
    addcld
    @0
    @9
    cc
    wcel
    @21
    @20
    @19
    @0
    @4
    @8
    @22
    @23
    subcld
    #
    @9
    @11
    c2
    divdir
    syl3an1
    syl3an2
    3anidm12
    mpanr12
    @0
    @14
    @5
    c2
    cdiv
    @0
    @5
    @4
    @4
    caddc
    co
    @9
    @4
    caddc
    co
    @8
    caddc
    co
    @14
    @0
    @4
    @22
    2timesd
    @0
    @4
    @8
    @4
    @22
    @23
    @22
    nppcand
    @0
    @9
    @4
    @8
    @24
    @22
    @23
    addassd
    3eqtr2rd
    oveq1d
    3eqtr2d
    @0
    @4
    c2
    @22
    @17
    @0
    2cn
    a1i
    @18
    @0
    2ne0
    a1i
    divcan3d
    eqtrd
end
