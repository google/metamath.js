include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "clcm.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "dvds0.mm"
include "ad2antrr.mm"
include "oveq1.mm"
include "0z.mm"
include "lcmcom.mm"
include "mpan2.mm"
include "lcm0val.mm"
include "eqtr3d.mm"
include "sylan9eqr.mm"
include "adantll.mm"
include "oveq2.mm"
include "adantlr.mm"
include "jaodan.mm"
include "breqtrrd.mm"
include "ad2antlr.mm"
include "jca.mm"
include "wn.mm"
include "cv.mm"
include "cn.mm"
include "crab.mm"
include "lcmcllem.mm"
include "wb.mm"
include "lcmn0cl.mm"
include "breq2.mm"
include "anbi12d.mm"
include "elrab3.mm"
include "syl.mm"
include "mpbid.mm"
include "pm2.61dan.mm"

theorem dvdslcm
  let cM: class M
  let cN: class N
  let cK: class K
  let vn: setvar n


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M || ( M lcm N ) /\ N || ( M lcm N ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cM
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wo
    #
    cM
    cM
    cN
    clcm
    co
    #
    cdvds
    wbr
    #
    cN
    @6
    cdvds
    wbr
    #
    wa
    #
    @2
    @5
    wa
    #
    @7
    @8
    @10
    cM
    cc0
    @6
    cdvds
    @0
    cM
    cc0
    cdvds
    wbr
    @1
    @5
    cM
    dvds0
    ad2antrr
    @2
    @3
    @6
    cc0
    wceq
    #
    @4
    @1
    @3
    @11
    @0
    @3
    @1
    @6
    cc0
    cN
    clcm
    co
    #
    cc0
    cM
    cc0
    cN
    clcm
    oveq1
    @1
    cN
    cc0
    clcm
    co
    #
    @12
    cc0
    @1
    cc0
    cz
    wcel
    @13
    @12
    wceq
    0z
    cN
    cc0
    lcmcom
    mpan2
    cN
    lcm0val
    eqtr3d
    sylan9eqr
    adantll
    @0
    @4
    @11
    @1
    @4
    @0
    @6
    cM
    cc0
    clcm
    co
    cc0
    cN
    cc0
    cM
    clcm
    oveq2
    cM
    lcm0val
    sylan9eqr
    adantlr
    jaodan
    #
    breqtrrd
    @10
    cN
    cc0
    @6
    cdvds
    @1
    cN
    cc0
    cdvds
    wbr
    @0
    @5
    cN
    dvds0
    ad2antlr
    @14
    breqtrrd
    jca
    @2
    @5
    wn
    wa
    #
    @6
    cM
    vn
    cv
    #
    cdvds
    wbr
    #
    cN
    @16
    cdvds
    wbr
    #
    wa
    #
    vn
    cn
    crab
    wcel
    #
    @9
    vn
    cM
    cN
    lcmcllem
    @15
    @6
    cn
    wcel
    @20
    @9
    wb
    cM
    cN
    lcmn0cl
    @19
    @9
    vn
    @6
    cn
    @16
    @6
    wceq
    @17
    @7
    @18
    @8
    @16
    @6
    cM
    cdvds
    breq2
    @16
    @6
    cN
    cdvds
    breq2
    anbi12d
    elrab3
    syl
    mpbid
    pm2.61dan
end
