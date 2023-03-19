include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "w3a.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "caddc.mm"
include "nn0cn.mm"
include "1cnd.mm"
include "subsub4d.mm"
include "1p1e2.mm"
include "oveq2i.mm"
include "syl6req.mm"
include "3ad2ant1.mm"
include "cn.mm"
include "wa.mm"
include "3simpa.mm"
include "elnnne0.mm"
include "sylibr.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "subeq0ad.mm"
include "biimpd.mm"
include "necon3d.mm"
include "imp.mm"
include "3adant2.mm"
include "sylanbrc.mm"
include "eqeltrd.mm"
include "wb.mm"
include "2nn0.mm"
include "jctl.mm"
include "nn0sub.mm"
include "mpbird.mm"

theorem nn0n0n1ge2
  let cN: class N


  assert |- ( ( N e. NN0 /\ N =/= 0 /\ N =/= 1 ) -> 2 <_ N )

  proof
    cN
    cn0
    wcel
    #
    cN
    cc0
    wne
    #
    cN
    c1
    wne
    #
    w3a
    #
    c2
    cN
    cle
    wbr
    #
    cN
    c2
    cmin
    co
    #
    cn0
    wcel
    #
    @3
    @5
    cN
    c1
    cmin
    co
    #
    c1
    cmin
    co
    #
    cn0
    @0
    @1
    @5
    @8
    wceq
    @2
    @0
    @8
    cN
    c1
    c1
    caddc
    co
    #
    cmin
    co
    @5
    @0
    cN
    c1
    c1
    cN
    nn0cn
    #
    @0
    1cnd
    #
    @11
    subsub4d
    @9
    c2
    cN
    cmin
    1p1e2
    oveq2i
    syl6req
    3ad2ant1
    @3
    @7
    cn
    wcel
    #
    @8
    cn0
    wcel
    @3
    @7
    cn0
    wcel
    #
    @7
    cc0
    wne
    #
    @12
    @3
    cN
    cn
    wcel
    #
    @13
    @3
    @0
    @1
    wa
    @15
    @0
    @1
    @2
    3simpa
    cN
    elnnne0
    sylibr
    cN
    nnm1nn0
    syl
    @0
    @2
    @14
    @1
    @0
    @2
    @14
    @0
    @7
    cc0
    cN
    c1
    @0
    @7
    cc0
    wceq
    cN
    c1
    wceq
    @0
    cN
    c1
    @10
    @11
    subeq0ad
    biimpd
    necon3d
    imp
    3adant2
    @7
    elnnne0
    sylanbrc
    @7
    nnm1nn0
    syl
    eqeltrd
    @3
    c2
    cn0
    wcel
    #
    @0
    wa
    #
    @4
    @6
    wb
    @0
    @1
    @17
    @2
    @0
    @16
    2nn0
    jctl
    3ad2ant1
    c2
    cN
    nn0sub
    syl
    mpbird
end
