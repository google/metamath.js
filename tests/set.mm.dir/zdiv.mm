include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cc0.mm"
include "wne.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cdiv.mm"
include "wb.mm"
include "nnne0.mm"
include "adantr.mm"
include "cc.mm"
include "wi.mm"
include "nncn.mm"
include "zcn.mm"
include "w3a.mm"
include "divcan3.mm"
include "3coml.mm"
include "3expa.mm"
include "sylan2.mm"
include "3adantl2.mm"
include "oveq1.mm"
include "sylan9req.mm"
include "simplr.mm"
include "eqeltrrd.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "divcan2.mm"
include "3com12.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "expcom.mm"
include "syl.mm"
include "impbid.mm"
include "3expia.mm"
include "syl2an.mm"
include "mpd.mm"

theorem zdiv
  let vk: setvar k
  let cM: class M
  let cN: class N

  disjoint M k
  disjoint N k
  assert |- ( ( M e. NN /\ N e. ZZ ) -> ( E. k e. ZZ ( M x. k ) = N <-> ( N / M ) e. ZZ ) )

  proof
    cM
    cn
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    cM
    cc0
    wne
    #
    cM
    vk
    cv
    #
    cmul
    co
    #
    cN
    wceq
    #
    vk
    cz
    wrex
    #
    cN
    cM
    cdiv
    co
    #
    cz
    wcel
    #
    wb
    #
    @0
    @2
    @1
    cM
    nnne0
    adantr
    @0
    cM
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    @2
    @9
    wi
    @1
    cM
    nncn
    cN
    zcn
    @10
    @11
    @2
    @9
    @10
    @11
    @2
    w3a
    #
    @6
    @8
    @12
    @5
    @8
    vk
    cz
    @12
    @3
    cz
    wcel
    #
    @5
    @8
    @12
    @13
    wa
    #
    @5
    wa
    @3
    @7
    cz
    @14
    @5
    @3
    @4
    cM
    cdiv
    co
    #
    @7
    @10
    @2
    @13
    @15
    @3
    wceq
    #
    @11
    @13
    @10
    @2
    wa
    @3
    cc
    wcel
    #
    @16
    @3
    zcn
    @10
    @2
    @17
    @16
    @17
    @10
    @2
    @16
    @3
    cM
    divcan3
    3coml
    3expa
    sylan2
    3adantl2
    @4
    cN
    cM
    cdiv
    oveq1
    sylan9req
    @12
    @13
    @5
    simplr
    eqeltrrd
    exp31
    rexlimdv
    @12
    cM
    @7
    cmul
    co
    #
    cN
    wceq
    #
    @8
    @6
    wi
    @11
    @10
    @2
    @19
    cN
    cM
    divcan2
    3com12
    @8
    @19
    @6
    @5
    @19
    vk
    @7
    cz
    @3
    @7
    wceq
    @4
    @18
    cN
    @3
    @7
    cM
    cmul
    oveq2
    eqeq1d
    rspcev
    expcom
    syl
    impbid
    3expia
    syl2an
    mpd
end
