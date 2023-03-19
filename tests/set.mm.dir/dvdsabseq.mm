include "cdvds.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "dvdszrcl.mm"
include "cc0.mm"
include "simpr.mm"
include "breq1.mm"
include "wb.mm"
include "0dvds.mm"
include "adantr.mm"
include "zcn.mm"
include "abs00ad.mm"
include "bicomd.mm"
include "bitrd.mm"
include "sylan9bb.mm"
include "fveq2.mm"
include "abs0.mm"
include "syl6eq.mm"
include "eqeq2d.mm"
include "bitr4d.mm"
include "syl5ib.mm"
include "expd.mm"
include "wn.mm"
include "cle.mm"
include "wne.mm"
include "simprl.mm"
include "adantl.mm"
include "neqne.mm"
include "dvdsleabs2.mm"
include "syl3anc.mm"
include "eqcom.mm"
include "syl5rbbr.mm"
include "eqeq1d.mm"
include "a1dd.mm"
include "expcomd.mm"
include "cr.mm"
include "abscld.mm"
include "letri3.mm"
include "syl2anr.mm"
include "syl5bb.mm"
include "biimprd.mm"
include "syld.mm"
include "a1d.mm"
include "pm2.61ian.mm"
include "com34.mm"
include "mpdd.mm"
include "mpcom.mm"
include "imp.mm"

theorem dvdsabseq
  let cM: class M
  let cN: class N


  assert |- ( ( M || N /\ N || M ) -> ( abs ` M ) = ( abs ` N ) )

  proof
    cM
    cN
    cdvds
    wbr
    #
    cN
    cM
    cdvds
    wbr
    #
    cM
    cabs
    cfv
    #
    cN
    cabs
    cfv
    #
    wceq
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    @0
    @1
    @4
    wi
    #
    cM
    cN
    dvdszrcl
    cN
    cc0
    wceq
    #
    @7
    @0
    @8
    wi
    @9
    @7
    wa
    #
    @0
    @1
    @4
    @0
    @1
    wa
    @1
    @10
    @4
    @0
    @1
    simpr
    @10
    @1
    @2
    cc0
    wceq
    #
    @4
    @9
    @1
    cc0
    cM
    cdvds
    wbr
    #
    @7
    @11
    cN
    cc0
    cM
    cdvds
    breq1
    @7
    @12
    cM
    cc0
    wceq
    #
    @11
    @5
    @12
    @13
    wb
    @6
    cM
    0dvds
    adantr
    @5
    @13
    @11
    wb
    @6
    @5
    @11
    @13
    @5
    cM
    cM
    zcn
    #
    abs00ad
    bicomd
    adantr
    bitrd
    sylan9bb
    @10
    @3
    cc0
    @2
    @9
    @3
    cc0
    wceq
    #
    @7
    @9
    @3
    cc0
    cabs
    cfv
    #
    cc0
    cN
    cc0
    cabs
    fveq2
    abs0
    syl6eq
    adantr
    eqeq2d
    bitr4d
    syl5ib
    expd
    @9
    wn
    #
    @7
    wa
    #
    @0
    @2
    @3
    cle
    wbr
    #
    @8
    @18
    @5
    @6
    cN
    cc0
    wne
    #
    @0
    @19
    wi
    @17
    @5
    @6
    simprl
    @7
    @6
    @17
    @5
    @6
    simpr
    #
    adantl
    @17
    @20
    @7
    cN
    cc0
    neqne
    adantr
    cM
    cN
    dvdsleabs2
    syl3anc
    @7
    @0
    @19
    @8
    wi
    wi
    @17
    @7
    @0
    @1
    @19
    @4
    @13
    @7
    @0
    @1
    @19
    @4
    wi
    #
    wi
    #
    wi
    @13
    @7
    wa
    #
    @1
    @0
    @22
    @24
    @1
    @0
    wa
    #
    @4
    @19
    @25
    @0
    @24
    @4
    @1
    @0
    simpr
    @24
    @0
    cc0
    @3
    wceq
    #
    @4
    @13
    @0
    cc0
    cN
    cdvds
    wbr
    #
    @7
    @26
    cM
    cc0
    cN
    cdvds
    breq1
    @6
    @27
    @26
    wb
    @5
    @6
    @27
    @9
    @26
    cN
    0dvds
    @26
    @15
    @6
    @9
    @3
    cc0
    eqcom
    @6
    cN
    cN
    zcn
    #
    abs00ad
    syl5rbbr
    bitrd
    adantl
    sylan9bb
    @24
    @2
    cc0
    @3
    @13
    @11
    @7
    @13
    @2
    @16
    cc0
    cM
    cc0
    cabs
    fveq2
    abs0
    syl6eq
    adantr
    eqeq1d
    bitr4d
    syl5ib
    a1dd
    expcomd
    @13
    wn
    #
    @7
    wa
    #
    @23
    @0
    @30
    @1
    @3
    @2
    cle
    wbr
    #
    @22
    @30
    @6
    @5
    cM
    cc0
    wne
    #
    @1
    @31
    wi
    @7
    @6
    @29
    @21
    adantl
    @29
    @5
    @6
    simprl
    @29
    @32
    @7
    cM
    cc0
    neqne
    adantr
    cN
    cM
    dvdsleabs2
    syl3anc
    @7
    @31
    @22
    wi
    @29
    @7
    @31
    @19
    @4
    @7
    @4
    @31
    @19
    wa
    #
    @4
    @3
    @2
    wceq
    #
    @7
    @33
    @2
    @3
    eqcom
    @6
    @3
    cr
    wcel
    @2
    cr
    wcel
    @34
    @33
    wb
    @5
    @6
    cN
    @28
    abscld
    @5
    cM
    @14
    abscld
    @3
    @2
    letri3
    syl2anr
    syl5bb
    biimprd
    expd
    adantl
    syld
    a1d
    pm2.61ian
    com34
    adantl
    mpdd
    pm2.61ian
    mpcom
    imp
end
