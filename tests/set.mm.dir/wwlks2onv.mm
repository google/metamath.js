include "wcel.mm"
include "cs3.mm"
include "c2.mm"
include "cwwlksnon.mm"
include "co.mm"
include "wa.mm"
include "w3a.mm"
include "wwlksonvtx.mm"
include "adantl.mm"
include "simprl.mm"
include "cwwlksn.mm"
include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wwlknon.mm"
include "cn0.mm"
include "cvtx.mm"
include "cword.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "wwlknbp1.mm"
include "s3fv1.mm"
include "eqcomd.mm"
include "cfzo.mm"
include "eqcomi.mm"
include "wrdeqi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "ctp.mm"
include "1ex.mm"
include "tpid2.mm"
include "c3.mm"
include "s3len.mm"
include "oveq2i.mm"
include "fzo0to3tp.mm"
include "eqtri.mm"
include "eleqtrri.mm"
include "wrdsymbcl.mm"
include "sylancl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "ex.mm"
include "3ad2ant2.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "sylbi.mm"
include "impcom.mm"
include "simprr.mm"
include "3jca.mm"
include "mpdan.mm"

theorem wwlks2onv
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cG: class G
  let cV: class V
  assume wwlks2onv.v: |- V = ( Vtx ` G )


  assert |- ( ( B e. U /\ <" A B C "> e. ( A ( 2 WWalksNOn G ) C ) ) -> ( A e. V /\ B e. V /\ C e. V ) )

  proof
    cB
    cU
    wcel
    #
    cA
    cB
    cC
    cs3
    #
    cA
    cC
    c2
    cG
    cwwlksnon
    co
    co
    wcel
    #
    wa
    #
    cA
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    wa
    #
    @4
    cB
    cV
    wcel
    #
    @5
    w3a
    @2
    @6
    @0
    cA
    cC
    cG
    c2
    cV
    @1
    wwlks2onv.v
    wwlksonvtx
    adantl
    @3
    @6
    wa
    @4
    @7
    @5
    @3
    @4
    @5
    simprl
    @3
    @7
    @6
    @2
    @0
    @7
    @2
    @1
    c2
    cG
    cwwlksn
    co
    wcel
    #
    cc0
    @1
    cfv
    cA
    wceq
    #
    c2
    @1
    cfv
    cC
    wceq
    #
    w3a
    @0
    @7
    wi
    #
    cA
    cC
    cG
    c2
    @1
    wwlknon
    @8
    @9
    @11
    @10
    @8
    c2
    cn0
    wcel
    #
    @1
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    @1
    chash
    cfv
    #
    c2
    c1
    caddc
    co
    wceq
    #
    w3a
    @11
    cG
    c2
    @1
    wwlknbp1
    @15
    @12
    @11
    @17
    @15
    @0
    @7
    @15
    @0
    wa
    cB
    c1
    @1
    cfv
    #
    cV
    @0
    cB
    @18
    wceq
    @15
    @0
    @18
    cB
    cA
    cB
    cC
    cU
    s3fv1
    eqcomd
    adantl
    @15
    @18
    cV
    wcel
    #
    @0
    @15
    @1
    cV
    cword
    #
    wcel
    #
    c1
    cc0
    @16
    cfzo
    co
    #
    wcel
    @19
    @15
    @21
    @14
    @20
    @1
    @13
    cV
    cV
    @13
    wwlks2onv.v
    eqcomi
    wrdeqi
    eleq2i
    biimpi
    c1
    cc0
    c1
    c2
    ctp
    #
    @22
    cc0
    c1
    c2
    1ex
    tpid2
    @22
    cc0
    c3
    cfzo
    co
    @23
    @16
    c3
    cc0
    cfzo
    cA
    cB
    cC
    s3len
    oveq2i
    fzo0to3tp
    eqtri
    eleqtrri
    c1
    cV
    @1
    wrdsymbcl
    sylancl
    adantr
    eqeltrd
    ex
    3ad2ant2
    syl
    3ad2ant1
    sylbi
    impcom
    adantr
    @3
    @4
    @5
    simprr
    3jca
    mpdan
end
