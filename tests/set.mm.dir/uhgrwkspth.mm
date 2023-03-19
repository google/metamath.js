include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
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
include "uhgrwkspthlem1.mm"
include "expcom.mm"
include "3ad2ant2.mm"
include "com12.mm"
include "3ad2ant1.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "istrl.mm"
include "sylanbrc.mm"
include "3simpc.mm"
include "adantl.mm"
include "adantr.mm"
include "uhgrwkspthlem2.mm"
include "syl3anc.mm"
include "isspth.mm"
include "3anass.mm"
include "wb.mm"
include "3simpa.mm"
include "eqid.mm"
include "isspthonpth.mm"
include "syl.mm"
include "mpbird.mm"
include "ex.mm"
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

theorem uhgrwkspth
  let cA: class A
  let cB: class B
  let cP: class P
  let cE: class E
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  assume uhgrwkspth.v: |- V = ( Vtx ` G )
  assume uhgrwkspth.e: |- E = ( Edg ` G )


  assert |- ( ( G e. W /\ ( # ` F ) = 1 /\ A =/= B ) -> ( F ( A ( WalksOn ` G ) B ) P <-> F ( A ( SPathsOn ` G ) B ) P ) )

  proof
    cG
    cW
    wcel
    #
    cF
    chash
    cfv
    #
    c1
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
    cA
    wceq
    #
    @1
    cP
    cfv
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
    @16
    @4
    @6
    @16
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
    @13
    @14
    w3a
    #
    @17
    @18
    @13
    @14
    wa
    #
    @19
    @17
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
    @18
    @17
    @12
    cF
    ccnv
    wfun
    #
    @21
    @12
    @13
    @14
    @10
    @11
    @4
    simpl31
    #
    @16
    @4
    @23
    @15
    @10
    @4
    @23
    wi
    #
    @11
    @12
    @13
    @25
    @14
    @4
    @12
    @23
    @2
    @0
    @12
    @23
    wi
    @3
    @12
    @2
    @23
    cP
    cF
    cG
    uhgrwkspthlem1
    expcom
    3ad2ant2
    com12
    3ad2ant1
    3ad2ant3
    imp
    cP
    cF
    cG
    istrl
    sylanbrc
    @17
    @12
    @2
    @3
    wa
    #
    @20
    @22
    @24
    @4
    @26
    @16
    @0
    @2
    @3
    3simpc
    adantl
    @16
    @20
    @4
    @15
    @10
    @20
    @11
    @12
    @13
    @14
    3simpc
    3ad2ant3
    adantr
    #
    cA
    cB
    cP
    cF
    cG
    uhgrwkspthlem2
    syl3anc
    cP
    cF
    cG
    isspth
    sylanbrc
    @27
    @18
    @13
    @14
    3anass
    sylanbrc
    @17
    @10
    @11
    wa
    #
    @6
    @19
    wb
    @16
    @28
    @4
    @10
    @11
    @15
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
    @15
    w3a
    @16
    cA
    cB
    cP
    cF
    cG
    @7
    @29
    wlkonprop
    @31
    @10
    @11
    @15
    @30
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
