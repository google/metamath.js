include "cusgr.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wne.mm"
include "w3a.mm"
include "cwlkson.mm"
include "co.mm"
include "wbr.mm"
include "cspthson.mm"
include "cvtx.mm"
include "wa.mm"
include "cvv.mm"
include "cwlks.mm"
include "cc0.mm"
include "cspths.mm"
include "ctrls.mm"
include "ccnv.mm"
include "wfun.mm"
include "simpl31.mm"
include "wi.mm"
include "simp2.mm"
include "simp3.mm"
include "neeq12d.mm"
include "bicomd.mm"
include "3anbi3d.mm"
include "usgr2wlkspthlem1.mm"
include "ex.mm"
include "3ad2ant1.mm"
include "sylbid.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "istrl.mm"
include "sylanbrc.mm"
include "usgr2wlkspthlem2.mm"
include "isspth.mm"
include "3simpc.mm"
include "adantr.mm"
include "3anass.mm"
include "wb.mm"
include "3simpa.mm"
include "eqid.mm"
include "isspthonpth.mm"
include "syl.mm"
include "mpbird.mm"
include "wlkonprop.mm"
include "3anim1i.mm"
include "syl11.mm"
include "cpthson.mm"
include "ctrlson.mm"
include "spthonpthon.mm"
include "pthontrlon.mm"
include "trlsonwlkon.mm"
include "3syl.mm"
include "impbid1.mm"

theorem usgr2wlkspth
  let cA: class A
  let cB: class B
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( ( G e. USGraph /\ ( # ` F ) = 2 /\ A =/= B ) -> ( F ( A ( WalksOn ` G ) B ) P <-> F ( A ( SPathsOn ` G ) B ) P ) )

  proof
    cG
    cusgr
    wcel
    #
    cF
    chash
    cfv
    #
    c2
    wceq
    #
    cA
    cB
    wne
    #
    w3a
    #
    cF
    cP
    cA
    cB
    cG
    cwlkson
    cfv
    co
    wbr
    #
    cF
    cP
    cA
    cB
    cG
    cspthson
    cfv
    co
    wbr
    #
    cA
    cG
    cvtx
    cfv
    #
    wcel
    #
    cB
    @7
    wcel
    #
    wa
    #
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    wa
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cc0
    cP
    cfv
    #
    cA
    wceq
    #
    @1
    cP
    cfv
    #
    cB
    wceq
    #
    w3a
    #
    w3a
    #
    @4
    @6
    @5
    @18
    @4
    @6
    @18
    @4
    wa
    #
    @6
    cF
    cP
    cG
    cspths
    cfv
    wbr
    #
    @14
    @16
    w3a
    #
    @19
    @20
    @14
    @16
    wa
    #
    @21
    @19
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    cP
    ccnv
    wfun
    #
    @20
    @19
    @12
    cF
    ccnv
    wfun
    #
    @23
    @12
    @14
    @16
    @10
    @11
    @4
    simpl31
    @18
    @4
    @25
    @17
    @10
    @4
    @25
    wi
    @11
    @17
    @4
    @0
    @2
    @13
    @15
    wne
    #
    w3a
    #
    @25
    @17
    @3
    @26
    @0
    @2
    @17
    @26
    @3
    @17
    @13
    cA
    @15
    cB
    @12
    @14
    @16
    simp2
    @12
    @14
    @16
    simp3
    neeq12d
    bicomd
    3anbi3d
    #
    @12
    @14
    @27
    @25
    wi
    @16
    @12
    @27
    @25
    cP
    cF
    cG
    usgr2wlkspthlem1
    ex
    3ad2ant1
    sylbid
    3ad2ant3
    imp
    cP
    cF
    cG
    istrl
    sylanbrc
    @18
    @4
    @24
    @17
    @10
    @4
    @24
    wi
    @11
    @17
    @4
    @27
    @24
    @28
    @12
    @14
    @27
    @24
    wi
    @16
    @12
    @27
    @24
    cP
    cF
    cG
    usgr2wlkspthlem2
    ex
    3ad2ant1
    sylbid
    3ad2ant3
    imp
    cP
    cF
    cG
    isspth
    sylanbrc
    @18
    @22
    @4
    @17
    @10
    @22
    @11
    @12
    @14
    @16
    3simpc
    3ad2ant3
    adantr
    @20
    @14
    @16
    3anass
    sylanbrc
    @19
    @10
    @11
    wa
    #
    @6
    @21
    wb
    @18
    @29
    @4
    @10
    @11
    @17
    3simpa
    adantr
    cA
    cB
    cP
    cF
    cG
    @7
    cvv
    cvv
    @7
    eqid
    #
    isspthonpth
    syl
    mpbird
    ex
    @5
    cG
    cvv
    wcel
    #
    @8
    @9
    w3a
    #
    @11
    @17
    w3a
    @18
    cA
    cB
    cP
    cF
    cG
    @7
    @30
    wlkonprop
    @32
    @10
    @11
    @17
    @31
    @8
    @9
    3simpc
    3anim1i
    syl
    syl11
    @6
    cF
    cP
    cA
    cB
    cG
    cpthson
    cfv
    co
    wbr
    cF
    cP
    cA
    cB
    cG
    ctrlson
    cfv
    co
    wbr
    @5
    cA
    cB
    cP
    cF
    cG
    spthonpthon
    cA
    cB
    cP
    cF
    cG
    pthontrlon
    cA
    cB
    cP
    cF
    cG
    trlsonwlkon
    3syl
    impbid1
end
