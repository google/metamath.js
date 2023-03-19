include "ceven.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wa.mm"
include "c1.mm"
include "cz.mm"
include "wb.mm"
include "evenz.mm"
include "zltp1le.mm"
include "syl2anr.mm"
include "wceq.mm"
include "wo.mm"
include "cr.mm"
include "zred.mm"
include "peano2re.mm"
include "syl.mm"
include "leloe.mm"
include "peano2zd.mm"
include "cc.mm"
include "zcnd.mm"
include "adantl.mm"
include "add1p1.mm"
include "breq1d.mm"
include "biimpd.mm"
include "sylbid.mm"
include "codd.mm"
include "wi.mm"
include "evenp1odd.mm"
include "wne.mm"
include "zneoALTV.mm"
include "eqneqall.mm"
include "eqcoms.mm"
include "syl5com.mm"
include "sylan2.mm"
include "jaod.mm"
include "3impia.mm"

theorem evenltle
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. Even /\ M e. Even /\ M < N ) -> ( M + 2 ) <_ N )

  proof
    cN
    ceven
    wcel
    #
    cM
    ceven
    wcel
    #
    cM
    cN
    clt
    wbr
    #
    cM
    c2
    caddc
    co
    #
    cN
    cle
    wbr
    #
    @0
    @1
    wa
    #
    @2
    cM
    c1
    caddc
    co
    #
    cN
    cle
    wbr
    #
    @4
    @1
    cM
    cz
    wcel
    cN
    cz
    wcel
    #
    @2
    @7
    wb
    @0
    cM
    evenz
    #
    cN
    evenz
    #
    cM
    cN
    zltp1le
    syl2anr
    @5
    @7
    @6
    cN
    clt
    wbr
    #
    @6
    cN
    wceq
    #
    wo
    #
    @4
    @1
    @6
    cr
    wcel
    #
    cN
    cr
    wcel
    @7
    @13
    wb
    @0
    @1
    cM
    cr
    wcel
    @14
    @1
    cM
    @9
    zred
    cM
    peano2re
    syl
    @0
    cN
    @10
    zred
    @6
    cN
    leloe
    syl2anr
    @5
    @11
    @4
    @12
    @5
    @11
    @6
    c1
    caddc
    co
    #
    cN
    cle
    wbr
    #
    @4
    @1
    @6
    cz
    wcel
    @8
    @11
    @16
    wb
    @0
    @1
    cM
    @9
    peano2zd
    @10
    @6
    cN
    zltp1le
    syl2anr
    @5
    @16
    @4
    @5
    @15
    @3
    cN
    cle
    @5
    cM
    cc
    wcel
    #
    @15
    @3
    wceq
    @1
    @17
    @0
    @1
    cM
    @9
    zcnd
    adantl
    cM
    add1p1
    syl
    breq1d
    biimpd
    sylbid
    @1
    @0
    @6
    codd
    wcel
    #
    @12
    @4
    wi
    cM
    evenp1odd
    @0
    @18
    wa
    cN
    @6
    wne
    #
    @12
    @4
    cN
    @6
    zneoALTV
    @19
    @4
    wi
    cN
    @6
    @4
    cN
    @6
    eqneqall
    eqcoms
    syl5com
    sylan2
    jaod
    sylbid
    sylbid
    3impia
end
