include "cn0.mm"
include "wcel.mm"
include "cv.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "cz.mm"
include "wrex.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "eleq1.mm"
include "cc0.mm"
include "cle.mm"
include "elnn0z.mm"
include "2tnp1ge0ge0.mm"
include "biimpd.mm"
include "imdistani.mm"
include "expcom.mm"
include "syl6ibr.mm"
include "simplbiim.mm"
include "syl6bir.mm"
include "com13.mm"
include "impcom.mm"
include "pm4.71rd.mm"
include "bicomd.mm"
include "rexbidva.mm"
include "wss.mm"
include "wb.mm"
include "nn0ssz.mm"
include "rexss.mm"
include "mp1i.mm"
include "nn0z.mm"
include "odd2np1.mm"
include "syl.mm"
include "3bitr4rd.mm"

theorem oddnn02np1
  let vn: setvar n
  let cN: class N

  disjoint N n
  assert |- ( N e. NN0 -> ( -. 2 || N <-> E. n e. NN0 ( ( 2 x. n ) + 1 ) = N ) )

  proof
    cN
    cn0
    wcel
    #
    vn
    cv
    #
    cn0
    wcel
    #
    c2
    @1
    cmul
    co
    c1
    caddc
    co
    #
    cN
    wceq
    #
    wa
    #
    vn
    cz
    wrex
    #
    @4
    vn
    cz
    wrex
    #
    @4
    vn
    cn0
    wrex
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    @0
    @5
    @4
    vn
    cz
    @0
    @1
    cz
    wcel
    #
    wa
    #
    @4
    @5
    @11
    @4
    @2
    @10
    @0
    @4
    @2
    wi
    @4
    @0
    @10
    @2
    @4
    @0
    @3
    cn0
    wcel
    #
    @10
    @2
    wi
    #
    @3
    cN
    cn0
    eleq1
    @12
    @3
    cz
    wcel
    cc0
    @3
    cle
    wbr
    #
    @13
    @3
    elnn0z
    @14
    @10
    @10
    cc0
    @1
    cle
    wbr
    #
    wa
    #
    @2
    @10
    @14
    @16
    @10
    @14
    @15
    @10
    @14
    @15
    @1
    2tnp1ge0ge0
    biimpd
    imdistani
    expcom
    @1
    elnn0z
    syl6ibr
    simplbiim
    syl6bir
    com13
    impcom
    pm4.71rd
    bicomd
    rexbidva
    cn0
    cz
    wss
    @8
    @6
    wb
    @0
    nn0ssz
    @4
    vn
    cn0
    cz
    rexss
    mp1i
    @0
    cN
    cz
    wcel
    @9
    @7
    wb
    cN
    nn0z
    vn
    cN
    odd2np1
    syl
    3bitr4rd
end
