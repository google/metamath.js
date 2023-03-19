include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cr.mm"
include "zre.mm"
include "peano2re.mm"
include "syl.mm"
include "rehalfcld.mm"
include "flltp1.mm"
include "flcld.mm"
include "zred.mm"
include "1red.mm"
include "readdcld.mm"
include "crp.mm"
include "2rp.mm"
include "a1i.mm"
include "ltdivmuld.mm"
include "mpbid.mm"
include "recnd.mm"
include "2timesd.mm"
include "oveq2d.mm"
include "2cnd.mm"
include "adddid.mm"
include "2re.mm"
include "remulcld.mm"
include "addassd.mm"
include "3eqtr4d.mm"
include "breqtrd.mm"
include "ltadd1d.mm"
include "mpbird.mm"
include "wb.mm"
include "2z.mm"
include "zmulcld.mm"
include "zleltp1.mm"
include "mpdan.mm"

theorem flhalf
  let cN: class N


  assert |- ( N e. ZZ -> N <_ ( 2 x. ( |_ ` ( ( N + 1 ) / 2 ) ) ) )

  proof
    cN
    cz
    wcel
    #
    cN
    c2
    cN
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    cN
    @4
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @0
    @7
    @1
    @6
    c1
    caddc
    co
    #
    clt
    wbr
    @0
    @1
    c2
    @3
    c1
    caddc
    co
    #
    cmul
    co
    #
    @8
    clt
    @0
    @2
    @9
    clt
    wbr
    #
    @1
    @10
    clt
    wbr
    @0
    @2
    cr
    wcel
    @11
    @0
    @1
    @0
    cN
    cr
    wcel
    @1
    cr
    wcel
    cN
    zre
    #
    cN
    peano2re
    syl
    #
    rehalfcld
    #
    @2
    flltp1
    syl
    @0
    @1
    @9
    c2
    @13
    @0
    @3
    c1
    @0
    @3
    @0
    @2
    @14
    flcld
    #
    zred
    #
    @0
    1red
    #
    readdcld
    c2
    crp
    wcel
    @0
    2rp
    a1i
    ltdivmuld
    mpbid
    @0
    @4
    c2
    c1
    cmul
    co
    #
    caddc
    co
    @4
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @10
    @8
    @0
    @18
    @19
    @4
    caddc
    @0
    c1
    @0
    c1
    @17
    recnd
    #
    2timesd
    oveq2d
    @0
    c2
    @3
    c1
    @0
    2cnd
    @0
    @3
    @16
    recnd
    @20
    adddid
    @0
    @4
    c1
    c1
    @0
    @4
    @0
    c2
    @3
    c2
    cr
    wcel
    @0
    2re
    a1i
    @16
    remulcld
    #
    recnd
    @20
    @20
    addassd
    3eqtr4d
    breqtrd
    @0
    cN
    @6
    c1
    @12
    @0
    @4
    c1
    @21
    @17
    readdcld
    @17
    ltadd1d
    mpbird
    @0
    @4
    cz
    wcel
    @5
    @7
    wb
    @0
    c2
    @3
    c2
    cz
    wcel
    @0
    2z
    a1i
    @15
    zmulcld
    cN
    @4
    zleltp1
    mpdan
    mpbird
end
