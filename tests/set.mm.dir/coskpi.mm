include "cz.mm"
include "wcel.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "ccos.mm"
include "cfv.mm"
include "cabs.mm"
include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "caddc.mm"
include "2t1e2.mm"
include "df-2.mm"
include "eqtr2i.mm"
include "cmin.mm"
include "cc.mm"
include "zcn.mm"
include "2cn.mm"
include "picn.mm"
include "mul12.mm"
include "mp3an23.mm"
include "syl.mm"
include "fveq2d.mm"
include "cos2kpi.mm"
include "cr.mm"
include "zre.mm"
include "pire.mm"
include "remulcl.mm"
include "sylancl.mm"
include "recnd.mm"
include "cos2t.mm"
include "3eqtr3rd.mm"
include "wb.mm"
include "recoscld.mm"
include "sqcld.mm"
include "mulcl.mm"
include "sylancr.mm"
include "ax-1cn.mm"
include "subadd.mm"
include "mpbid.mm"
include "syl5reqr.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "2cnne0.mm"
include "mulcan.mm"
include "sq1.mm"
include "syl6eqr.mm"
include "1re.mm"
include "sqabs.mm"
include "abs1.mm"
include "syl6eq.mm"

theorem coskpi
  let cK: class K


  assert |- ( K e. ZZ -> ( abs ` ( cos ` ( K x. _pi ) ) ) = 1 )

  proof
    cK
    cz
    wcel
    #
    cK
    cpi
    cmul
    co
    #
    ccos
    cfv
    #
    cabs
    cfv
    #
    c1
    cabs
    cfv
    #
    c1
    @0
    @2
    c2
    cexp
    co
    #
    c1
    c2
    cexp
    co
    #
    wceq
    #
    @3
    @4
    wceq
    #
    @0
    @5
    c1
    @6
    @0
    c2
    @5
    cmul
    co
    #
    c2
    c1
    cmul
    co
    #
    wceq
    #
    @5
    c1
    wceq
    #
    @0
    @10
    c1
    c1
    caddc
    co
    #
    @9
    @10
    c2
    @13
    2t1e2
    df-2
    eqtr2i
    @0
    @9
    c1
    cmin
    co
    #
    c1
    wceq
    #
    @13
    @9
    wceq
    #
    @0
    cK
    c2
    cpi
    cmul
    co
    cmul
    co
    #
    ccos
    cfv
    c2
    @1
    cmul
    co
    #
    ccos
    cfv
    #
    c1
    @14
    @0
    @17
    @18
    ccos
    @0
    cK
    cc
    wcel
    #
    @17
    @18
    wceq
    #
    cK
    zcn
    @20
    c2
    cc
    wcel
    #
    cpi
    cc
    wcel
    @21
    2cn
    picn
    cK
    c2
    cpi
    mul12
    mp3an23
    syl
    fveq2d
    cK
    cos2kpi
    @0
    @1
    cc
    wcel
    @19
    @14
    wceq
    @0
    @1
    @0
    cK
    cr
    wcel
    cpi
    cr
    wcel
    @1
    cr
    wcel
    cK
    zre
    pire
    cK
    cpi
    remulcl
    sylancl
    #
    recnd
    @1
    cos2t
    syl
    3eqtr3rd
    @0
    @9
    cc
    wcel
    #
    @15
    @16
    wb
    #
    @0
    @22
    @5
    cc
    wcel
    #
    @24
    2cn
    @0
    @2
    @0
    @2
    @0
    @1
    @23
    recoscld
    #
    recnd
    sqcld
    #
    c2
    @5
    mulcl
    sylancr
    @24
    c1
    cc
    wcel
    #
    @29
    @25
    ax-1cn
    ax-1cn
    @9
    c1
    c1
    subadd
    mp3an23
    syl
    mpbid
    syl5reqr
    @0
    @26
    @11
    @12
    wb
    #
    @28
    @26
    @29
    @22
    c2
    cc0
    wne
    wa
    @30
    ax-1cn
    2cnne0
    @5
    c1
    c2
    mulcan
    mp3an23
    syl
    mpbid
    sq1
    syl6eqr
    @0
    @2
    cr
    wcel
    c1
    cr
    wcel
    @7
    @8
    wb
    @27
    1re
    @2
    c1
    sqabs
    sylancl
    mpbid
    abs1
    syl6eq
end
