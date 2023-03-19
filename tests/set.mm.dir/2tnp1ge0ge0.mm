include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "cdiv.mm"
include "cr.mm"
include "clt.mm"
include "wb.mm"
include "2z.mm"
include "a1i.mm"
include "id.mm"
include "zmulcld.mm"
include "peano2zd.mm"
include "zred.mm"
include "2re.mm"
include "2pos.mm"
include "ge0div.mm"
include "syl3anc.mm"
include "cc.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "zcnd.mm"
include "1cnd.mm"
include "2cnne0.mm"
include "divdir.mm"
include "zcn.mm"
include "2cnd.mm"
include "2ne0.mm"
include "divcan3d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "zre.mm"
include "halfre.mm"
include "readdcld.mm"
include "halfge0.mm"
include "addge01d.mm"
include "mpbii.mm"
include "1red.mm"
include "halflt1.mm"
include "ltadd2dd.mm"
include "btwnzge0.mm"
include "syl22anc.mm"
include "3bitrd.mm"

theorem 2tnp1ge0ge0
  let cN: class N


  assert |- ( N e. ZZ -> ( 0 <_ ( ( 2 x. N ) + 1 ) <-> 0 <_ N ) )

  proof
    cN
    cz
    wcel
    #
    cc0
    c2
    cN
    cmul
    co
    #
    c1
    caddc
    co
    #
    cle
    wbr
    #
    cc0
    @2
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    cc0
    cN
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    cc0
    cN
    cle
    wbr
    #
    @0
    @2
    cr
    wcel
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    @3
    @5
    wb
    @0
    @2
    @0
    @1
    @0
    c2
    cN
    c2
    cz
    wcel
    @0
    2z
    a1i
    @0
    id
    #
    zmulcld
    #
    peano2zd
    zred
    @10
    @0
    2re
    a1i
    @11
    @0
    2pos
    a1i
    @2
    c2
    ge0div
    syl3anc
    @0
    @4
    @7
    cc0
    cle
    @0
    @4
    @1
    c2
    cdiv
    co
    #
    @6
    caddc
    co
    #
    @7
    @0
    @1
    cc
    wcel
    c1
    cc
    wcel
    c2
    cc
    wcel
    c2
    cc0
    wne
    #
    wa
    #
    @4
    @15
    wceq
    @0
    @1
    @13
    zcnd
    @0
    1cnd
    @17
    @0
    2cnne0
    a1i
    @1
    c1
    c2
    divdir
    syl3anc
    @0
    @14
    cN
    @6
    caddc
    @0
    cN
    c2
    cN
    zcn
    @0
    2cnd
    @16
    @0
    2ne0
    a1i
    divcan3d
    oveq1d
    eqtrd
    breq2d
    @0
    @7
    cr
    wcel
    @0
    cN
    @7
    cle
    wbr
    #
    @7
    cN
    c1
    caddc
    co
    clt
    wbr
    @8
    @9
    wb
    @0
    cN
    @6
    cN
    zre
    #
    @6
    cr
    wcel
    @0
    halfre
    a1i
    #
    readdcld
    @12
    @0
    cc0
    @6
    cle
    wbr
    @18
    halfge0
    @0
    cN
    @6
    @19
    @20
    addge01d
    mpbii
    @0
    @6
    c1
    cN
    @20
    @0
    1red
    @19
    @6
    c1
    clt
    wbr
    @0
    halflt1
    a1i
    ltadd2dd
    @7
    cN
    btwnzge0
    syl22anc
    3bitrd
end
