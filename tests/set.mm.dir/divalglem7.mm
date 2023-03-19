include "cc0.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wcel.mm"
include "cz.mm"
include "wne.mm"
include "cmul.mm"
include "caddc.mm"
include "wn.mm"
include "wi.mm"
include "cif.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "notbid.mm"
include "imbi2d.mm"
include "neeq1.mm"
include "oveq2d.mm"
include "imbi12d.mm"
include "cn.mm"
include "nnabscl.mm"
include "mp2an.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "0z.mm"
include "0le0.mm"
include "nngt0i.mm"
include "w3a.mm"
include "wb.mm"
include "nnzi.mm"
include "elfzm11.mm"
include "mpbir3an.mm"
include "elimel.mm"
include "divalglem6.mm"
include "dedth2h.mm"

theorem divalglem7
  let cD: class D
  let cK: class K
  let cX: class X
  assume divalglem7.1: |- D e. ZZ
  assume divalglem7.2: |- D =/= 0


  assert |- ( ( X e. ( 0 ... ( ( abs ` D ) - 1 ) ) /\ K e. ZZ ) -> ( K =/= 0 -> -. ( X + ( K x. ( abs ` D ) ) ) e. ( 0 ... ( ( abs ` D ) - 1 ) ) ) )

  proof
    cX
    cc0
    cD
    cabs
    cfv
    #
    c1
    cmin
    co
    cfz
    co
    #
    wcel
    #
    cK
    cz
    wcel
    #
    cK
    cc0
    wne
    #
    cX
    cK
    @0
    cmul
    co
    #
    caddc
    co
    #
    @1
    wcel
    #
    wn
    #
    wi
    @4
    @2
    cX
    cc0
    cif
    #
    @5
    caddc
    co
    #
    @1
    wcel
    #
    wn
    #
    wi
    @3
    cK
    cc0
    cif
    #
    cc0
    wne
    #
    @9
    @13
    @0
    cmul
    co
    #
    caddc
    co
    #
    @1
    wcel
    #
    wn
    #
    wi
    cX
    cK
    cc0
    cc0
    cX
    @9
    wceq
    #
    @8
    @12
    @4
    @19
    @7
    @11
    @19
    @6
    @10
    @1
    cX
    @9
    @5
    caddc
    oveq1
    eleq1d
    notbid
    imbi2d
    cK
    @13
    wceq
    #
    @4
    @14
    @12
    @18
    cK
    @13
    cc0
    neeq1
    @20
    @11
    @17
    @20
    @10
    @16
    @1
    @20
    @5
    @15
    @9
    caddc
    cK
    @13
    @0
    cmul
    oveq1
    oveq2d
    eleq1d
    notbid
    imbi12d
    @0
    @13
    @9
    cD
    cz
    wcel
    cD
    cc0
    wne
    @0
    cn
    wcel
    divalglem7.1
    divalglem7.2
    cD
    nnabscl
    mp2an
    #
    cX
    cc0
    @1
    cc0
    @1
    wcel
    #
    cc0
    cz
    wcel
    #
    cc0
    cc0
    cle
    wbr
    #
    cc0
    @0
    clt
    wbr
    #
    0z
    0le0
    @0
    @21
    nngt0i
    @23
    @0
    cz
    wcel
    @22
    @23
    @24
    @25
    w3a
    wb
    0z
    @0
    @21
    nnzi
    cc0
    cc0
    @0
    elfzm11
    mp2an
    mpbir3an
    elimel
    cK
    cc0
    cz
    0z
    elimel
    divalglem6
    dedth2h
end
