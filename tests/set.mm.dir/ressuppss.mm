include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "csupp.mm"
include "co.mm"
include "cab.mm"
include "cin.mm"
include "elin.mm"
include "simprbi.mm"
include "dmres.mm"
include "eleq2s.mm"
include "ad2antrl.mm"
include "wi.mm"
include "wss.mm"
include "wceq.mm"
include "snssi.mm"
include "resima2.mm"
include "syl.mm"
include "neeq1d.mm"
include "biimpd.mm"
include "adantld.mm"
include "wn.mm"
include "pm2.24.mm"
include "adantr.mm"
include "sylbi.mm"
include "com12.mm"
include "pm2.61i.mm"
include "jca.mm"
include "ex.mm"
include "ss2abdv.mm"
include "df-rab.mm"
include "3sstr4g.mm"
include "cvv.mm"
include "resexg.mm"
include "suppval.mm"
include "sylan.mm"
include "3sstr4d.mm"

theorem ressuppss
  let cB: class B
  let cF: class F
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vb: setvar b


  assert |- ( ( F e. V /\ Z e. W ) -> ( ( F |` B ) supp Z ) C_ ( F supp Z ) )

  proof
    cF
    cV
    wcel
    #
    cZ
    cW
    wcel
    #
    wa
    #
    cF
    cB
    cres
    #
    vb
    cv
    #
    csn
    #
    cima
    #
    cZ
    csn
    #
    wne
    #
    vb
    @3
    cdm
    #
    crab
    #
    cF
    @5
    cima
    #
    @7
    wne
    #
    vb
    cF
    cdm
    #
    crab
    #
    @3
    cZ
    csupp
    co
    #
    cF
    cZ
    csupp
    co
    @2
    @4
    @9
    wcel
    #
    @8
    wa
    #
    vb
    cab
    @4
    @13
    wcel
    #
    @12
    wa
    #
    vb
    cab
    @10
    @14
    @2
    @17
    @19
    vb
    @2
    @17
    @19
    @2
    @17
    wa
    #
    @18
    @12
    @16
    @18
    @2
    @8
    @18
    @4
    cB
    @13
    cin
    #
    @9
    @4
    @21
    wcel
    #
    @4
    cB
    wcel
    #
    @18
    @4
    cB
    @13
    elin
    #
    simprbi
    cF
    cB
    dmres
    #
    eleq2s
    ad2antrl
    @23
    @20
    @12
    wi
    @23
    @17
    @12
    @2
    @23
    @8
    @12
    @16
    @23
    @8
    @12
    @23
    @6
    @11
    @7
    @23
    @5
    cB
    wss
    @6
    @11
    wceq
    @4
    cB
    snssi
    cF
    @5
    cB
    resima2
    syl
    neeq1d
    biimpd
    adantld
    adantld
    @20
    @23
    wn
    #
    @12
    @16
    @26
    @12
    wi
    #
    @2
    @8
    @27
    @4
    @21
    @9
    @22
    @23
    @18
    wa
    @27
    @24
    @23
    @27
    @18
    @23
    @12
    pm2.24
    adantr
    sylbi
    @25
    eleq2s
    ad2antrl
    com12
    pm2.61i
    jca
    ex
    ss2abdv
    @8
    vb
    @9
    df-rab
    @12
    vb
    @13
    df-rab
    3sstr4g
    @0
    @3
    cvv
    wcel
    @1
    @15
    @10
    wceq
    cF
    cB
    cV
    resexg
    vb
    cvv
    cW
    @3
    cZ
    suppval
    sylan
    vb
    cV
    cW
    cF
    cZ
    suppval
    3sstr4d
end
