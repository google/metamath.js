include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "clt.mm"
include "cr.mm"
include "wb.mm"
include "nn0re.mm"
include "leloe.mm"
include "syl2an.mm"
include "elnn0.mm"
include "wi.mm"
include "nnsub.mm"
include "ex.mm"
include "nngt0.mm"
include "nncn.mm"
include "subid1d.mm"
include "id.mm"
include "eqeltrd.mm"
include "2thd.mm"
include "breq1.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "bibi12d.mm"
include "syl5ibr.mm"
include "jaoi.mm"
include "sylbi.mm"
include "nn0nlt0.mm"
include "pm2.21d.mm"
include "0re.mm"
include "posdif.mm"
include "sylancl.mm"
include "impbid.mm"
include "breq2.mm"
include "oveq1.mm"
include "syl5ibrcom.mm"
include "jaod.mm"
include "syl5bi.mm"
include "imp.mm"
include "cc.mm"
include "nn0cn.mm"
include "subeq0.mm"
include "syl2anr.mm"
include "eqcom.mm"
include "syl6rbb.mm"
include "orbi12d.mm"
include "bitrd.mm"
include "syl6bbr.mm"

theorem nn0sub
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN0 /\ N e. NN0 ) -> ( M <_ N <-> ( N - M ) e. NN0 ) )

  proof
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cM
    cN
    cle
    wbr
    #
    cN
    cM
    cmin
    co
    #
    cn
    wcel
    #
    @4
    cc0
    wceq
    #
    wo
    #
    @4
    cn0
    wcel
    @2
    @3
    cM
    cN
    clt
    wbr
    #
    cM
    cN
    wceq
    #
    wo
    #
    @7
    @0
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    @3
    @10
    wb
    @1
    cM
    nn0re
    #
    cN
    nn0re
    cM
    cN
    leloe
    syl2an
    @2
    @8
    @5
    @9
    @6
    @0
    @1
    @8
    @5
    wb
    #
    @1
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    @0
    @13
    cN
    elnn0
    @0
    @14
    @13
    @15
    @0
    cM
    cn
    wcel
    #
    cM
    cc0
    wceq
    #
    wo
    @14
    @13
    wi
    #
    cM
    elnn0
    @16
    @18
    @17
    @16
    @14
    @13
    cM
    cN
    nnsub
    ex
    @14
    @13
    @17
    cc0
    cN
    clt
    wbr
    #
    cN
    cc0
    cmin
    co
    #
    cn
    wcel
    #
    wb
    @14
    @19
    @21
    cN
    nngt0
    @14
    @20
    cN
    cn
    @14
    cN
    cN
    nncn
    subid1d
    @14
    id
    eqeltrd
    2thd
    @17
    @8
    @19
    @5
    @21
    cM
    cc0
    cN
    clt
    breq1
    @17
    @4
    @20
    cn
    cM
    cc0
    cN
    cmin
    oveq2
    eleq1d
    bibi12d
    syl5ibr
    jaoi
    sylbi
    @0
    @13
    @15
    cM
    cc0
    clt
    wbr
    #
    cc0
    cM
    cmin
    co
    #
    cn
    wcel
    #
    wb
    @0
    @22
    @24
    @0
    @22
    @24
    cM
    nn0nlt0
    pm2.21d
    @24
    @22
    @0
    cc0
    @23
    clt
    wbr
    #
    @23
    nngt0
    @0
    @11
    cc0
    cr
    wcel
    @22
    @25
    wb
    @12
    0re
    cM
    cc0
    posdif
    sylancl
    syl5ibr
    impbid
    @15
    @8
    @22
    @5
    @24
    cN
    cc0
    cM
    clt
    breq2
    @15
    @4
    @23
    cn
    cN
    cc0
    cM
    cmin
    oveq1
    eleq1d
    bibi12d
    syl5ibrcom
    jaod
    syl5bi
    imp
    @2
    @6
    cN
    cM
    wceq
    #
    @9
    @1
    cN
    cc
    wcel
    cM
    cc
    wcel
    @6
    @26
    wb
    @0
    cN
    nn0cn
    cM
    nn0cn
    cN
    cM
    subeq0
    syl2anr
    cN
    cM
    eqcom
    syl6rbb
    orbi12d
    bitrd
    @4
    elnn0
    syl6bbr
end
