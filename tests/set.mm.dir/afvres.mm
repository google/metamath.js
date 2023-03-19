include "cdm.mm"
include "wcel.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wa.mm"
include "cafv.mm"
include "wceq.mm"
include "cfv.mm"
include "cin.mm"
include "elin.mm"
include "biimpri.mm"
include "dmres.mm"
include "syl6eleqr.mm"
include "ex.mm"
include "snssi.mm"
include "resabs1d.mm"
include "eqcomd.mm"
include "funeqd.mm"
include "biimpd.mm"
include "anim12d.mm"
include "impcom.mm"
include "wdfat.mm"
include "df-dfat.mm"
include "afvfundmfveq.mm"
include "sylbir.mm"
include "syl.mm"
include "fvres.mm"
include "adantl.mm"
include "adantr.mm"
include "3eqtrd.mm"
include "wn.mm"
include "cvv.mm"
include "wi.mm"
include "pm3.4.mm"
include "sylbi.mm"
include "eleq2s.mm"
include "com12.mm"
include "con3d.mm"
include "afvnfundmuv.mm"
include "sylnbir.mm"
include "eqtrd.mm"
include "pm2.61ian.mm"

theorem afvres
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( A e. B -> ( ( F |` B ) ''' A ) = ( F ''' A ) )

  proof
    cA
    cF
    cdm
    #
    wcel
    #
    cF
    cA
    csn
    #
    cres
    #
    wfun
    #
    wa
    #
    cA
    cB
    wcel
    #
    cA
    cF
    cB
    cres
    #
    cafv
    #
    cA
    cF
    cafv
    #
    wceq
    @5
    @6
    wa
    #
    @8
    cA
    @7
    cfv
    #
    cA
    cF
    cfv
    #
    @9
    @10
    cA
    @7
    cdm
    #
    wcel
    #
    @7
    @2
    cres
    #
    wfun
    #
    wa
    #
    @8
    @11
    wceq
    #
    @6
    @5
    @17
    @6
    @1
    @14
    @4
    @16
    @6
    @1
    @14
    @6
    @1
    wa
    #
    cA
    cB
    @0
    cin
    #
    @13
    cA
    @20
    wcel
    #
    @19
    cA
    cB
    @0
    elin
    #
    biimpri
    cF
    cB
    dmres
    #
    syl6eleqr
    ex
    @6
    @4
    @16
    @6
    @3
    @15
    @6
    @15
    @3
    @6
    cF
    @2
    cB
    cA
    cB
    snssi
    resabs1d
    #
    eqcomd
    funeqd
    biimpd
    anim12d
    impcom
    @17
    cA
    @7
    wdfat
    #
    @18
    cA
    @7
    df-dfat
    #
    cA
    @7
    afvfundmfveq
    sylbir
    syl
    @6
    @11
    @12
    wceq
    @5
    cA
    cB
    cF
    fvres
    adantl
    @5
    @12
    @9
    wceq
    @6
    @5
    @9
    @12
    @5
    cA
    cF
    wdfat
    #
    @9
    @12
    wceq
    cA
    cF
    df-dfat
    #
    cA
    cF
    afvfundmfveq
    sylbir
    eqcomd
    adantr
    3eqtrd
    @5
    wn
    #
    @6
    wa
    #
    @8
    cvv
    @9
    @30
    @17
    wn
    #
    @8
    cvv
    wceq
    #
    @6
    @29
    @31
    @6
    @17
    @5
    @6
    @14
    @1
    @16
    @4
    @14
    @6
    @1
    @6
    @1
    wi
    #
    cA
    @20
    @13
    @21
    @19
    @33
    @22
    @6
    @1
    pm3.4
    sylbi
    @23
    eleq2s
    com12
    @6
    @16
    @4
    @6
    @15
    @3
    @24
    funeqd
    biimpd
    anim12d
    con3d
    impcom
    @17
    @25
    @32
    @26
    cA
    @7
    afvnfundmuv
    sylnbir
    syl
    @29
    cvv
    @9
    wceq
    @6
    @29
    @9
    cvv
    @5
    @27
    @9
    cvv
    wceq
    @28
    cA
    cF
    afvnfundmuv
    sylnbir
    eqcomd
    adantr
    eqtrd
    pm2.61ian
end
