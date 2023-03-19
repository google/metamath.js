include "cc.mm"
include "wcel.mm"
include "cim.mm"
include "cfv.mm"
include "c2.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "ccj.mm"
include "cmin.mm"
include "wceq.mm"
include "imcl.mm"
include "recnd.mm"
include "cc0.mm"
include "wne.mm"
include "2mulicn.mm"
include "2muline0.mm"
include "divcan4.mm"
include "mp3an23.mm"
include "syl.mm"
include "cre.mm"
include "caddc.mm"
include "recl.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addcld.mm"
include "subsubd.mm"
include "replim.mm"
include "remim.mm"
include "oveq12d.mm"
include "2timesd.mm"
include "mulcom.mm"
include "mpan2.mm"
include "2cn.mm"
include "mulass.mm"
include "mp3an12.mm"
include "eqtrd.mm"
include "pncan2d.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "3eqtr4rd.mm"
include "eqtr3d.mm"

theorem imval2
  let cA: class A


  assert |- ( A e. CC -> ( Im ` A ) = ( ( A - ( * ` A ) ) / ( 2 x. _i ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cim
    cfv
    #
    c2
    ci
    cmul
    co
    #
    cmul
    co
    #
    @2
    cdiv
    co
    #
    @1
    cA
    cA
    ccj
    cfv
    #
    cmin
    co
    #
    @2
    cdiv
    co
    @0
    @1
    cc
    wcel
    #
    @4
    @1
    wceq
    #
    @0
    @1
    cA
    imcl
    recnd
    #
    @7
    @2
    cc
    wcel
    #
    @2
    cc0
    wne
    @8
    2mulicn
    2muline0
    @1
    @2
    divcan4
    mp3an23
    syl
    @0
    @3
    @6
    @2
    cdiv
    @0
    cA
    cre
    cfv
    #
    ci
    @1
    cmul
    co
    #
    caddc
    co
    #
    @11
    @12
    cmin
    co
    #
    cmin
    co
    @13
    @11
    cmin
    co
    #
    @12
    caddc
    co
    #
    @6
    @3
    @0
    @13
    @11
    @12
    @0
    @11
    @12
    @0
    @11
    cA
    recl
    recnd
    #
    @0
    ci
    cc
    wcel
    #
    @7
    @12
    cc
    wcel
    ax-icn
    @9
    ci
    @1
    mulcl
    sylancr
    #
    addcld
    @17
    @19
    subsubd
    @0
    cA
    @13
    @5
    @14
    cmin
    cA
    replim
    cA
    remim
    oveq12d
    @0
    c2
    @12
    cmul
    co
    #
    @12
    @12
    caddc
    co
    @3
    @16
    @0
    @12
    @19
    2timesd
    @0
    @7
    @3
    @20
    wceq
    @9
    @7
    @3
    @2
    @1
    cmul
    co
    #
    @20
    @7
    @10
    @3
    @21
    wceq
    2mulicn
    @1
    @2
    mulcom
    mpan2
    c2
    cc
    wcel
    @18
    @7
    @21
    @20
    wceq
    2cn
    ax-icn
    c2
    ci
    @1
    mulass
    mp3an12
    eqtrd
    syl
    @0
    @15
    @12
    @12
    caddc
    @0
    @11
    @12
    @17
    @19
    pncan2d
    oveq1d
    3eqtr4d
    3eqtr4rd
    oveq1d
    eqtr3d
end
