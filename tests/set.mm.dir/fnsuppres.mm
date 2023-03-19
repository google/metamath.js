include "cun.mm"
include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "wss.mm"
include "cres.mm"
include "csn.mm"
include "cxp.mm"
include "wral.mm"
include "csupp.mm"
include "co.mm"
include "fndm.mm"
include "rabeq.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "sseq1d.mm"
include "unss.mm"
include "ssrab2.mm"
include "biantrur.mm"
include "rabun2.mm"
include "sseq1i.mm"
include "3bitr4ri.mm"
include "wi.mm"
include "rabss.mm"
include "wn.mm"
include "fvres.mm"
include "adantl.mm"
include "simp2r.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "eqeq12d.mm"
include "wb.mm"
include "nne.mm"
include "a1i.mm"
include "id.mm"
include "simp3.mm"
include "minel.mm"
include "syl2anr.mm"
include "mtt.mm"
include "3bitr2rd.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "wfun.mm"
include "fnfun.mm"
include "3anim1i.mm"
include "3expb.mm"
include "suppval1.mm"
include "3adant3.mm"
include "simp1.mm"
include "ssun2.mm"
include "fnssres.mm"
include "syl2anc.mm"
include "fnconstg.mm"
include "3ad2ant2.mm"
include "eqfnfv.mm"
include "3bitr4d.mm"

theorem fnsuppres
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let cW: class W
  let cZ: class Z
  let va: setvar a


  assert |- ( ( F Fn ( A u. B ) /\ ( F e. W /\ Z e. V ) /\ ( A i^i B ) = (/) ) -> ( ( F supp Z ) C_ A <-> ( F |` B ) = ( B X. { Z } ) ) )

  proof
    cF
    cA
    cB
    cun
    #
    wfn
    #
    cF
    cW
    wcel
    #
    cZ
    cV
    wcel
    #
    wa
    #
    cA
    cB
    cin
    c0
    wceq
    #
    w3a
    #
    va
    cv
    #
    cF
    cfv
    #
    cZ
    wne
    #
    va
    cF
    cdm
    #
    crab
    #
    cA
    wss
    #
    @7
    cF
    cB
    cres
    #
    cfv
    #
    @7
    cB
    cZ
    csn
    cxp
    #
    cfv
    #
    wceq
    #
    va
    cB
    wral
    #
    cF
    cZ
    csupp
    co
    #
    cA
    wss
    @13
    @15
    wceq
    #
    @6
    @12
    @9
    va
    @0
    crab
    #
    cA
    wss
    #
    @18
    @6
    @11
    @21
    cA
    @1
    @4
    @11
    @21
    wceq
    #
    @5
    @1
    @10
    @0
    wceq
    @23
    @0
    cF
    fndm
    @9
    va
    @10
    @0
    rabeq
    syl
    3ad2ant1
    sseq1d
    @22
    @9
    va
    cB
    crab
    #
    cA
    wss
    #
    @6
    @18
    @9
    va
    cA
    crab
    #
    cA
    wss
    #
    @25
    wa
    @26
    @24
    cun
    #
    cA
    wss
    @25
    @22
    @26
    @24
    cA
    unss
    @27
    @25
    @9
    va
    cA
    ssrab2
    biantrur
    @21
    @28
    cA
    @9
    va
    cA
    cB
    rabun2
    sseq1i
    3bitr4ri
    @25
    @9
    @7
    cA
    wcel
    #
    wi
    #
    va
    cB
    wral
    @6
    @18
    @9
    va
    cB
    cA
    rabss
    @6
    @30
    @17
    va
    cB
    @6
    @7
    cB
    wcel
    #
    wa
    #
    @17
    @8
    cZ
    wceq
    #
    @9
    wn
    #
    @30
    @32
    @14
    @8
    @16
    cZ
    @31
    @14
    @8
    wceq
    @6
    @7
    cB
    cF
    fvres
    adantl
    @6
    @3
    @31
    @16
    cZ
    wceq
    @1
    @2
    @3
    @5
    simp2r
    cB
    cZ
    @7
    cV
    fvconst2g
    sylan
    eqeq12d
    @34
    @33
    wb
    @32
    @8
    cZ
    nne
    a1i
    @32
    @29
    wn
    #
    @34
    @30
    wb
    @31
    @31
    @5
    @35
    @6
    @31
    id
    @1
    @4
    @5
    simp3
    @7
    cB
    cA
    minel
    syl2anr
    @29
    @9
    mtt
    syl
    3bitr2rd
    ralbidva
    syl5bb
    syl5bb
    bitrd
    @6
    @19
    @11
    cA
    @1
    @4
    @19
    @11
    wceq
    #
    @5
    @1
    @4
    wa
    cF
    wfun
    #
    @2
    @3
    w3a
    #
    @36
    @1
    @2
    @3
    @38
    @1
    @37
    @2
    @3
    @0
    cF
    fnfun
    3anim1i
    3expb
    va
    cW
    cV
    cF
    cZ
    suppval1
    syl
    3adant3
    sseq1d
    @6
    @13
    cB
    wfn
    #
    @15
    cB
    wfn
    #
    @20
    @18
    wb
    @6
    @1
    cB
    @0
    wss
    #
    @39
    @1
    @4
    @5
    simp1
    @41
    @6
    cB
    cA
    ssun2
    a1i
    @0
    cB
    cF
    fnssres
    syl2anc
    @4
    @1
    @40
    @5
    @3
    @40
    @2
    cB
    cZ
    cV
    fnconstg
    adantl
    3ad2ant2
    va
    cB
    @13
    @15
    eqfnfv
    syl2anc
    3bitr4d
end
