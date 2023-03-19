include "cumgr.mm"
include "wcel.mm"
include "cclwwlk.mm"
include "cfv.mm"
include "c2.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cn0.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "w3a.mm"
include "cvv.mm"
include "cvtx.mm"
include "cword.mm"
include "c0.mm"
include "eqid.mm"
include "clwwlkbp.mm"
include "adantl.mm"
include "lencl.mm"
include "3ad2ant2.mm"
include "wi.mm"
include "wceq.mm"
include "hasheq0.mm"
include "bicomd.mm"
include "necon3bid.mm"
include "biimpd.mm"
include "a1i.mm"
include "3imp.mm"
include "cpr.mm"
include "cedg.mm"
include "clwwlk1loop.mm"
include "expcom.mm"
include "umgredgne.mm"
include "eqneqall.mm"
include "mpsyl.mm"
include "syl6.mm"
include "com23.mm"
include "imp4c.mm"
include "wn.mm"
include "neqne.mm"
include "a1d.mm"
include "pm2.61i.mm"
include "3jca.mm"
include "mpdan.mm"
include "nn0n0n1ge2.mm"
include "syl.mm"
include "ex.mm"

theorem umgrclwwlkge2
  let cP: class P
  let cG: class G


  assert |- ( G e. UMGraph -> ( P e. ( ClWWalks ` G ) -> 2 <_ ( # ` P ) ) )

  proof
    cG
    cumgr
    wcel
    #
    cP
    cG
    cclwwlk
    cfv
    wcel
    #
    c2
    cP
    chash
    cfv
    #
    cle
    wbr
    #
    @0
    @1
    wa
    #
    @2
    cn0
    wcel
    #
    @2
    cc0
    wne
    #
    @2
    c1
    wne
    #
    w3a
    #
    @3
    @4
    cG
    cvv
    wcel
    #
    cP
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    cP
    c0
    wne
    #
    w3a
    #
    @8
    @1
    @14
    @0
    cG
    @10
    cP
    @10
    eqid
    clwwlkbp
    adantl
    @4
    @14
    wa
    #
    @5
    @6
    @7
    @14
    @5
    @4
    @12
    @9
    @5
    @13
    @10
    cP
    lencl
    3ad2ant2
    adantl
    @14
    @6
    @4
    @9
    @12
    @13
    @6
    @12
    @13
    @6
    wi
    wi
    @9
    @12
    @13
    @6
    @12
    cP
    c0
    @2
    cc0
    @12
    @2
    cc0
    wceq
    cP
    c0
    wceq
    cP
    @11
    hasheq0
    bicomd
    necon3bid
    biimpd
    a1i
    3imp
    adantl
    @2
    c1
    wceq
    #
    @15
    @7
    wi
    @16
    @0
    @1
    @14
    @7
    @16
    @1
    @0
    @14
    @7
    wi
    #
    @16
    @1
    cc0
    cP
    cfv
    #
    @18
    cpr
    cG
    cedg
    cfv
    #
    wcel
    #
    @0
    @17
    wi
    @1
    @16
    @20
    cG
    cP
    clwwlk1loop
    expcom
    @0
    @20
    @17
    @18
    @18
    wceq
    @0
    @20
    wa
    @18
    @18
    wne
    @17
    @18
    eqid
    @19
    cG
    @18
    @18
    @19
    eqid
    umgredgne
    @17
    @18
    @18
    eqneqall
    mpsyl
    expcom
    syl6
    com23
    imp4c
    @16
    wn
    @7
    @15
    @2
    c1
    neqne
    a1d
    pm2.61i
    3jca
    mpdan
    @2
    nn0n0n1ge2
    syl
    ex
end
