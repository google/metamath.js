include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cz.mm"
include "wrex.mm"
include "cdvds.mm"
include "wbr.mm"
include "wi.mm"
include "eleq1.mm"
include "cc0.mm"
include "clt.mm"
include "simpr.mm"
include "cr.mm"
include "cle.mm"
include "2re.mm"
include "a1i.mm"
include "zre.mm"
include "adantl.mm"
include "0le2.mm"
include "nngt0.mm"
include "adantr.mm"
include "prodgt0.mm"
include "syl22anc.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "ex.mm"
include "syl6bir.mm"
include "com13.mm"
include "impcom.mm"
include "pm4.71rd.mm"
include "bicomd.mm"
include "rexbidva.mm"
include "wss.mm"
include "wb.mm"
include "nnssz.mm"
include "rexss.mm"
include "mp1i.mm"
include "even2n.mm"
include "3bitr4rd.mm"

theorem evennn2n
  let vn: setvar n
  let cN: class N

  disjoint N n
  assert |- ( N e. NN -> ( 2 || N <-> E. n e. NN ( 2 x. n ) = N ) )

  proof
    cN
    cn
    wcel
    #
    vn
    cv
    #
    cn
    wcel
    #
    c2
    @1
    cmul
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
    cn
    wrex
    #
    c2
    cN
    cdvds
    wbr
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
    cn
    wcel
    #
    @10
    @2
    wi
    @3
    cN
    cn
    eleq1
    @12
    @10
    @2
    @12
    @10
    wa
    #
    @10
    cc0
    @1
    clt
    wbr
    #
    @2
    @12
    @10
    simpr
    @13
    c2
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    cc0
    c2
    cle
    wbr
    #
    cc0
    @3
    clt
    wbr
    #
    @14
    @15
    @13
    2re
    a1i
    @10
    @16
    @12
    @1
    zre
    adantl
    @17
    @13
    0le2
    a1i
    @12
    @18
    @10
    @3
    nngt0
    adantr
    c2
    @1
    prodgt0
    syl22anc
    @1
    elnnz
    sylanbrc
    ex
    syl6bir
    com13
    impcom
    pm4.71rd
    bicomd
    rexbidva
    cn
    cz
    wss
    @8
    @6
    wb
    @0
    nnssz
    @4
    vn
    cn
    cz
    rexss
    mp1i
    @9
    @7
    wb
    @0
    vn
    cN
    even2n
    a1i
    3bitr4rd
end
