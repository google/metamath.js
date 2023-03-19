include "cz.mm"
include "wcel.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wb.mm"
include "wral.mm"
include "wceq.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "zltlem1.mm"
include "adantrr.mm"
include "adantrl.mm"
include "bibi12d.mm"
include "ancoms.mm"
include "ralbidva.mm"
include "wi.mm"
include "peano2zm.mm"
include "zextle.mm"
include "3expia.mm"
include "syl2an.mm"
include "cc.mm"
include "zcn.mm"
include "ax-1cn.mm"
include "subcan2.mm"
include "mp3an3.mm"
include "sylibd.mm"
include "sylbid.mm"
include "3impia.mm"

theorem zextlt
  let vk: setvar k
  let cM: class M
  let cN: class N

  disjoint M k
  disjoint N k
  assert |- ( ( M e. ZZ /\ N e. ZZ /\ A. k e. ZZ ( k < M <-> k < N ) ) -> M = N )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    vk
    cv
    #
    cM
    clt
    wbr
    #
    @2
    cN
    clt
    wbr
    #
    wb
    #
    vk
    cz
    wral
    #
    cM
    cN
    wceq
    #
    @0
    @1
    wa
    #
    @6
    @2
    cM
    c1
    cmin
    co
    #
    cle
    wbr
    #
    @2
    cN
    c1
    cmin
    co
    #
    cle
    wbr
    #
    wb
    #
    vk
    cz
    wral
    #
    @7
    @8
    @5
    @13
    vk
    cz
    @2
    cz
    wcel
    #
    @8
    @5
    @13
    wb
    @15
    @8
    wa
    @3
    @10
    @4
    @12
    @15
    @0
    @3
    @10
    wb
    @1
    @2
    cM
    zltlem1
    adantrr
    @15
    @1
    @4
    @12
    wb
    @0
    @2
    cN
    zltlem1
    adantrl
    bibi12d
    ancoms
    ralbidva
    @8
    @14
    @9
    @11
    wceq
    #
    @7
    @0
    @9
    cz
    wcel
    #
    @11
    cz
    wcel
    #
    @14
    @16
    wi
    @1
    cM
    peano2zm
    cN
    peano2zm
    @17
    @18
    @14
    @16
    vk
    @9
    @11
    zextle
    3expia
    syl2an
    @0
    cM
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    @16
    @7
    wb
    #
    @1
    cM
    zcn
    cN
    zcn
    @19
    @20
    c1
    cc
    wcel
    @21
    ax-1cn
    cM
    cN
    c1
    subcan2
    mp3an3
    syl2an
    sylibd
    sylbid
    3impia
end
