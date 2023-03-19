include "cgbow.mm"
include "wcel.mm"
include "c5.mm"
include "clt.mm"
include "wbr.mm"
include "c7.mm"
include "cle.mm"
include "gbowgt5.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cn.mm"
include "wi.mm"
include "gbowpos.mm"
include "cz.mm"
include "wb.mm"
include "5nn.mm"
include "nnzi.mm"
include "nnz.mm"
include "zltp1le.mm"
include "sylancr.mm"
include "biimpd.mm"
include "syl.mm"
include "c6.mm"
include "wceq.mm"
include "wo.mm"
include "5p1e6.mm"
include "breq1i.mm"
include "cr.mm"
include "6re.mm"
include "nnred.mm"
include "leloe.mm"
include "syl5bb.mm"
include "6nn.mm"
include "nnzd.mm"
include "wa.mm"
include "6p1e7.mm"
include "syl6ib.mm"
include "codd.mm"
include "cv.mm"
include "cprime.mm"
include "wrex.mm"
include "isgbow.mm"
include "eleq1.mm"
include "ceven.mm"
include "wn.mm"
include "6even.mm"
include "evennodd.mm"
include "pm2.21.mm"
include "mp2b.mm"
include "syl6bir.mm"
include "com12.mm"
include "adantr.mm"
include "sylbi.mm"
include "jaod.mm"
include "sylbid.mm"
include "syld.mm"
include "mpd.mm"

theorem gbowge7
  let cZ: class Z
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. GoldbachOddW -> 7 <_ Z )

  proof
    cZ
    cgbow
    wcel
    #
    c5
    cZ
    clt
    wbr
    #
    c7
    cZ
    cle
    wbr
    #
    cZ
    gbowgt5
    @0
    @1
    c5
    c1
    caddc
    co
    #
    cZ
    cle
    wbr
    #
    @2
    @0
    cZ
    cn
    wcel
    #
    @1
    @4
    wi
    cZ
    gbowpos
    #
    @5
    @1
    @4
    @5
    c5
    cz
    wcel
    cZ
    cz
    wcel
    #
    @1
    @4
    wb
    c5
    5nn
    nnzi
    cZ
    nnz
    c5
    cZ
    zltp1le
    sylancr
    biimpd
    syl
    @0
    @4
    c6
    cZ
    clt
    wbr
    #
    c6
    cZ
    wceq
    #
    wo
    #
    @2
    @4
    c6
    cZ
    cle
    wbr
    #
    @0
    @10
    @3
    c6
    cZ
    cle
    5p1e6
    breq1i
    @0
    c6
    cr
    wcel
    cZ
    cr
    wcel
    @11
    @10
    wb
    6re
    @0
    cZ
    @6
    nnred
    c6
    cZ
    leloe
    sylancr
    syl5bb
    @0
    @8
    @2
    @9
    @0
    @8
    c6
    c1
    caddc
    co
    #
    cZ
    cle
    wbr
    #
    @2
    @0
    c6
    cz
    wcel
    #
    @7
    @8
    @13
    wi
    c6
    6nn
    nnzi
    @0
    cZ
    @6
    nnzd
    @14
    @7
    wa
    @8
    @13
    c6
    cZ
    zltp1le
    biimpd
    sylancr
    @12
    c7
    cZ
    cle
    6p1e7
    breq1i
    syl6ib
    @0
    cZ
    codd
    wcel
    #
    cZ
    vp
    cv
    vq
    cv
    caddc
    co
    vr
    cv
    caddc
    co
    wceq
    vr
    cprime
    wrex
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    #
    wa
    @9
    @2
    wi
    #
    cZ
    vr
    vq
    vp
    isgbow
    @15
    @17
    @16
    @9
    @15
    @2
    @9
    @15
    c6
    codd
    wcel
    #
    @2
    c6
    cZ
    codd
    eleq1
    c6
    ceven
    wcel
    @18
    wn
    @18
    @2
    wi
    6even
    c6
    evennodd
    @18
    @2
    pm2.21
    mp2b
    syl6bir
    com12
    adantr
    sylbi
    jaod
    sylbid
    syld
    mpd
end
