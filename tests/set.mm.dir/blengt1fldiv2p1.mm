include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "wo.mm"
include "cuz.mm"
include "cfv.mm"
include "cblen.mm"
include "cfl.mm"
include "wceq.mm"
include "eluz2nn.mm"
include "nneop.mm"
include "syl.mm"
include "wi.mm"
include "wa.mm"
include "cmin.mm"
include "cn0.mm"
include "nnnn0.mm"
include "blennn0em1.mm"
include "sylan2.mm"
include "ancoms.mm"
include "oveq1d.mm"
include "cz.mm"
include "nnz.mm"
include "flid.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "adantr.mm"
include "cc.mm"
include "blennnelnn.mm"
include "nncnd.mm"
include "npcan1.mm"
include "adantl.mm"
include "3eqtr3rd.mm"
include "expcom.mm"
include "syl11.mm"
include "blennngt2o2.mm"
include "eluzge2nn0.mm"
include "nn0ofldiv2.mm"
include "syl2anr.mm"
include "eqtrd.mm"
include "ex.mm"
include "jaoi.mm"
include "mpcom.mm"

theorem blengt1fldiv2p1
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. ( ZZ>= ` 2 ) -> ( #b ` N ) = ( ( #b ` ( |_ ` ( N / 2 ) ) ) + 1 ) )

  proof
    cN
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    cN
    c1
    caddc
    co
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    wo
    #
    cN
    c2
    cuz
    cfv
    wcel
    #
    cN
    cblen
    cfv
    #
    @0
    cfl
    cfv
    #
    cblen
    cfv
    #
    c1
    caddc
    co
    #
    wceq
    #
    @5
    cN
    cn
    wcel
    #
    @4
    cN
    eluz2nn
    #
    cN
    nneop
    syl
    @1
    @5
    @10
    wi
    @3
    @11
    @1
    @10
    @5
    @1
    @11
    @10
    @1
    @11
    wa
    #
    @0
    cblen
    cfv
    #
    c1
    caddc
    co
    #
    @6
    c1
    cmin
    co
    #
    c1
    caddc
    co
    #
    @9
    @6
    @13
    @14
    @16
    c1
    caddc
    @11
    @1
    @14
    @16
    wceq
    #
    @1
    @11
    @0
    cn0
    wcel
    @18
    @0
    nnnn0
    cN
    blennn0em1
    sylan2
    ancoms
    oveq1d
    @1
    @15
    @9
    wceq
    @11
    @1
    @14
    @8
    c1
    caddc
    @1
    @0
    @7
    cblen
    @1
    @7
    @0
    @1
    @0
    cz
    wcel
    @7
    @0
    wceq
    @0
    nnz
    @0
    flid
    syl
    eqcomd
    fveq2d
    oveq1d
    adantr
    @11
    @17
    @6
    wceq
    #
    @1
    @11
    @6
    cc
    wcel
    @19
    @11
    @6
    cN
    blennnelnn
    nncnd
    @6
    npcan1
    syl
    adantl
    3eqtr3rd
    expcom
    @12
    syl11
    @3
    @5
    @10
    @3
    @5
    wa
    #
    @6
    cN
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cblen
    cfv
    #
    c1
    caddc
    co
    #
    @9
    @5
    @3
    @6
    @23
    wceq
    #
    @3
    @5
    @2
    cn0
    wcel
    #
    @24
    @2
    nnnn0
    #
    cN
    blennngt2o2
    sylan2
    ancoms
    @20
    @22
    @8
    c1
    caddc
    @20
    @21
    @7
    cblen
    @20
    @7
    @21
    @5
    cN
    cn0
    wcel
    @25
    @7
    @21
    wceq
    @3
    cN
    eluzge2nn0
    @26
    cN
    nn0ofldiv2
    syl2anr
    eqcomd
    fveq2d
    oveq1d
    eqtrd
    ex
    jaoi
    mpcom
end
