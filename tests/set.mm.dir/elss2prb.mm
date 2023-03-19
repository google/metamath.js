include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cpr.mm"
include "wrex.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "hash2prb.mm"
include "wss.mm"
include "wi.mm"
include "elpwi.mm"
include "ssrexv.mm"
include "syl.mm"
include "reximdv.mm"
include "syld.mm"
include "sylbid.mm"
include "imp.mm"
include "prelpwi.mm"
include "adantr.mm"
include "wb.mm"
include "eleq1.mm"
include "ad2antll.mm"
include "mpbird.mm"
include "hashprg.mm"
include "biimpcd.mm"
include "impcom.mm"
include "eqtrd.mm"
include "jca.mm"
include "ex.mm"
include "rexlimivv.mm"
include "impbii.mm"
include "bitri.mm"

theorem elss2prb
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cV: class V

  disjoint P x
  disjoint P y
  disjoint P z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint V x
  disjoint V y
  disjoint V z
  assert |- ( P e. { z e. ~P V | ( # ` z ) = 2 } <-> E. x e. V E. y e. V ( x =/= y /\ P = { x , y } ) )

  proof
    cP
    vz
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    vz
    cV
    cpw
    #
    crab
    wcel
    cP
    @3
    wcel
    #
    cP
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    cP
    @8
    @9
    cpr
    #
    wceq
    #
    wa
    #
    vy
    cV
    wrex
    #
    vx
    cV
    wrex
    #
    @2
    @6
    vz
    cP
    @3
    @0
    cP
    wceq
    @1
    @5
    c2
    @0
    cP
    chash
    fveq2
    eqeq1d
    elrab
    @7
    @15
    @4
    @6
    @15
    @4
    @6
    @13
    vy
    cP
    wrex
    #
    vx
    cP
    wrex
    #
    @15
    cP
    @3
    vx
    vy
    hash2prb
    @4
    @17
    @16
    vx
    cV
    wrex
    #
    @15
    @4
    cP
    cV
    wss
    #
    @17
    @18
    wi
    cP
    cV
    elpwi
    #
    @16
    vx
    cP
    cV
    ssrexv
    syl
    @4
    @16
    @14
    vx
    cV
    @4
    @19
    @16
    @14
    wi
    @20
    @13
    vy
    cP
    cV
    ssrexv
    syl
    reximdv
    syld
    sylbid
    imp
    @13
    @7
    vx
    vy
    cV
    cV
    @8
    cV
    wcel
    @9
    cV
    wcel
    wa
    #
    @13
    @7
    @21
    @13
    wa
    #
    @4
    @6
    @22
    @4
    @11
    @3
    wcel
    #
    @21
    @23
    @13
    @8
    @9
    cV
    prelpwi
    adantr
    @12
    @4
    @23
    wb
    @21
    @10
    cP
    @11
    @3
    eleq1
    ad2antll
    mpbird
    @22
    @5
    @11
    chash
    cfv
    #
    c2
    @12
    @5
    @24
    wceq
    @21
    @10
    cP
    @11
    chash
    fveq2
    ad2antll
    @13
    @21
    @24
    c2
    wceq
    #
    @10
    @21
    @25
    wi
    @12
    @21
    @10
    @25
    @8
    @9
    cV
    cV
    hashprg
    biimpcd
    adantr
    impcom
    eqtrd
    jca
    ex
    rexlimivv
    impbii
    bitri
end
