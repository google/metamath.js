include "cn0.mm"
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
include "cle.mm"
include "simpr.mm"
include "cr.mm"
include "clt.mm"
include "2re.mm"
include "a1i.mm"
include "zre.mm"
include "adantl.mm"
include "2pos.mm"
include "nn0ge0.mm"
include "adantr.mm"
include "prodge0.mm"
include "syl22anc.mm"
include "elnn0z.mm"
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
include "nn0ssz.mm"
include "rexss.mm"
include "mp1i.mm"
include "even2n.mm"
include "3bitr4rd.mm"

theorem evennn02n
  let vn: setvar n
  let cN: class N

  disjoint N n
  assert |- ( N e. NN0 -> ( 2 || N <-> E. n e. NN0 ( 2 x. n ) = N ) )

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
    @3
    cN
    cn0
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
    cle
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
    clt
    wbr
    #
    cc0
    @3
    cle
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
    2pos
    a1i
    @12
    @18
    @10
    @3
    nn0ge0
    adantr
    c2
    @1
    prodge0
    syl22anc
    @1
    elnn0z
    sylanbrc
    ex
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
