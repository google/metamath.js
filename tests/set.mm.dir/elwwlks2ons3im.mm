include "c2.mm"
include "cwwlksnon.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfv.mm"
include "cs3.mm"
include "wceq.mm"
include "wwlksonvtx.mm"
include "cwwlksn.mm"
include "cc0.mm"
include "w3a.mm"
include "wi.mm"
include "wwlknon.mm"
include "cn0.mm"
include "cvtx.mm"
include "cword.mm"
include "chash.mm"
include "caddc.mm"
include "wwlknbp1.mm"
include "c3.mm"
include "2p1e3.mm"
include "eqeq2i.mm"
include "cfzo.mm"
include "ctp.mm"
include "1ex.mm"
include "tpid2.mm"
include "fzo0to3tp.mm"
include "eleqtrri.mm"
include "oveq2.mm"
include "syl5eleqr.mm"
include "wrdsymbcl.mm"
include "sylan2.mm"
include "3ad2ant1.mm"
include "simpl1r.mm"
include "simpl.mm"
include "eqidd.mm"
include "simpr.mm"
include "3jca.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "wb.mm"
include "eqcomi.mm"
include "wrdeqi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "simpl3l.mm"
include "adantl.mm"
include "simpl3r.mm"
include "eqwrds3.mm"
include "syl13anc.mm"
include "mpbir2and.mm"
include "jca.mm"
include "mpdan.mm"
include "3exp.mm"
include "sylan2b.mm"
include "3adant1.mm"
include "syl.mm"
include "3impib.mm"
include "sylbi.mm"
include "mpd.mm"

theorem elwwlks2ons3im
  let cA: class A
  let cC: class C
  let cG: class G
  let cV: class V
  let cW: class W
  assume wwlks2onv.v: |- V = ( Vtx ` G )


  assert |- ( W e. ( A ( 2 WWalksNOn G ) C ) -> ( W = <" A ( W ` 1 ) C "> /\ ( W ` 1 ) e. V ) )

  proof
    cW
    cA
    cC
    c2
    cG
    cwwlksnon
    co
    co
    wcel
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
    cW
    cA
    c1
    cW
    cfv
    #
    cC
    cs3
    wceq
    #
    @4
    cV
    wcel
    #
    wa
    #
    cA
    cC
    cG
    c2
    cV
    cW
    wwlks2onv.v
    wwlksonvtx
    @0
    cW
    c2
    cG
    cwwlksn
    co
    wcel
    #
    cc0
    cW
    cfv
    cA
    wceq
    #
    c2
    cW
    cfv
    cC
    wceq
    #
    w3a
    @3
    @7
    wi
    #
    cA
    cC
    cG
    c2
    cW
    wwlknon
    @8
    @9
    @10
    @11
    @8
    c2
    cn0
    wcel
    #
    cW
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    cW
    chash
    cfv
    #
    c2
    c1
    caddc
    co
    #
    wceq
    #
    w3a
    @9
    @10
    wa
    #
    @11
    wi
    #
    cG
    c2
    cW
    wwlknbp1
    @15
    @18
    @20
    @12
    @18
    @15
    @16
    c3
    wceq
    #
    @20
    @17
    c3
    @16
    2p1e3
    eqeq2i
    @15
    @21
    wa
    #
    @19
    @3
    @7
    @22
    @19
    @3
    w3a
    #
    @4
    @13
    wcel
    #
    @7
    @22
    @19
    @24
    @3
    @21
    @15
    c1
    cc0
    @16
    cfzo
    co
    #
    wcel
    @24
    @21
    c1
    cc0
    c3
    cfzo
    co
    #
    @25
    c1
    cc0
    c1
    c2
    ctp
    @26
    cc0
    c1
    c2
    1ex
    tpid2
    fzo0to3tp
    eleqtrri
    @16
    c3
    cc0
    cfzo
    oveq2
    syl5eleqr
    c1
    @13
    cW
    wrdsymbcl
    sylan2
    3ad2ant1
    @23
    @24
    wa
    #
    @5
    @6
    @27
    @5
    @21
    @9
    @4
    @4
    wceq
    #
    @10
    w3a
    #
    @15
    @21
    @19
    @3
    @24
    simpl1r
    @23
    @29
    @24
    @19
    @22
    @29
    @3
    @19
    @9
    @28
    @10
    @9
    @10
    simpl
    @19
    @4
    eqidd
    @9
    @10
    simpr
    3jca
    3ad2ant2
    adantr
    @27
    cW
    cV
    cword
    #
    wcel
    #
    @1
    @6
    @2
    @5
    @21
    @29
    wa
    wb
    @23
    @31
    @24
    @22
    @19
    @31
    @3
    @15
    @31
    @21
    @15
    @31
    @14
    @30
    cW
    @13
    cV
    cV
    @13
    wwlks2onv.v
    eqcomi
    #
    wrdeqi
    eleq2i
    biimpi
    adantr
    3ad2ant1
    adantr
    @1
    @2
    @22
    @19
    @24
    simpl3l
    @24
    @6
    @23
    @24
    @6
    @13
    cV
    @4
    @32
    eleq2i
    biimpi
    adantl
    #
    @1
    @2
    @22
    @19
    @24
    simpl3r
    cA
    @4
    cC
    cV
    cW
    eqwrds3
    syl13anc
    mpbir2and
    @33
    jca
    mpdan
    3exp
    sylan2b
    3adant1
    syl
    3impib
    sylbi
    mpd
end
