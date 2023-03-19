include "wcel.mm"
include "wne.mm"
include "cv.mm"
include "clsm.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "clsa.mm"
include "wrex.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "eqid.mm"
include "clvec.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "islshpat.mm"
include "wi.mm"
include "simp12.mm"
include "wpss.mm"
include "wss.mm"
include "lssss.mm"
include "simp13.mm"
include "df-pss.mm"
include "sylanbrc.mm"
include "wb.mm"
include "psseq2.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "lcv2.mm"
include "mpbid.mm"
include "simp3.mm"
include "breqtrd.mm"
include "jca.mm"
include "rexlimdv3a.mm"
include "3exp.mm"
include "3impd.mm"
include "simprl.mm"
include "adantr.mm"
include "lss1.mm"
include "simprr.mm"
include "lcvpss.mm"
include "pssned.mm"
include "lcvat.mm"
include "3jca.mm"
include "ex.mm"
include "impbid.mm"
include "bitrd.mm"

theorem islshpcv
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cU: class U
  let cH: class H
  let cV: class V
  let cW: class W
  let vq: setvar q
  assume islshpcv.v: |- V = ( Base ` W )
  assume islshpcv.s: |- S = ( LSubSp ` W )
  assume islshpcv.h: |- H = ( LSHyp ` W )
  assume islshpcv.c: |- C = ( <oL ` W )
  assume islshpcv.w: |- ( ph -> W e. LVec )


  assert |- ( ph -> ( U e. H <-> ( U e. S /\ U C V ) ) )

  proof
    wph
    cU
    cH
    wcel
    cU
    cS
    wcel
    #
    cU
    cV
    wne
    #
    cU
    vq
    cv
    #
    cW
    clsm
    cfv
    #
    co
    #
    cV
    wceq
    #
    vq
    cW
    clsa
    cfv
    #
    wrex
    #
    w3a
    #
    @0
    cU
    cV
    cC
    wbr
    #
    wa
    #
    wph
    @6
    @3
    cS
    cU
    cH
    cV
    cW
    vq
    islshpcv.v
    islshpcv.s
    @3
    eqid
    #
    islshpcv.h
    @6
    eqid
    #
    wph
    cW
    clvec
    wcel
    #
    cW
    clmod
    wcel
    #
    islshpcv.w
    cW
    lveclmod
    syl
    #
    islshpat
    wph
    @8
    @10
    wph
    @0
    @1
    @7
    @10
    wph
    @0
    @1
    @7
    @10
    wi
    wph
    @0
    @1
    w3a
    #
    @5
    @10
    vq
    @6
    @16
    @2
    @6
    wcel
    #
    @5
    w3a
    #
    @0
    @9
    wph
    @0
    @1
    @17
    @5
    simp12
    #
    @18
    cU
    @4
    cV
    cC
    @18
    cU
    @4
    wpss
    #
    cU
    @4
    cC
    wbr
    @18
    @20
    cU
    cV
    wpss
    #
    @18
    cU
    cV
    wss
    #
    @1
    @21
    @18
    @0
    @22
    @19
    cS
    cU
    cV
    cW
    islshpcv.v
    islshpcv.s
    lssss
    syl
    wph
    @0
    @1
    @17
    @5
    simp13
    cU
    cV
    df-pss
    sylanbrc
    @5
    @16
    @20
    @21
    wb
    @17
    @4
    cV
    cU
    psseq2
    3ad2ant3
    mpbird
    @18
    @6
    cC
    @3
    @2
    cS
    cU
    cW
    islshpcv.s
    @11
    @12
    islshpcv.c
    @16
    @17
    @13
    @5
    wph
    @0
    @13
    @1
    islshpcv.w
    3ad2ant1
    3ad2ant1
    @19
    @16
    @17
    @5
    simp2
    lcv2
    mpbid
    @16
    @17
    @5
    simp3
    breqtrd
    jca
    rexlimdv3a
    3exp
    3impd
    wph
    @10
    @8
    wph
    @10
    wa
    #
    @0
    @1
    @7
    wph
    @0
    @9
    simprl
    #
    @23
    cU
    cV
    @23
    cC
    cS
    cU
    cV
    cW
    clvec
    islshpcv.s
    islshpcv.c
    wph
    @13
    @10
    islshpcv.w
    adantr
    @24
    @23
    @14
    cV
    cS
    wcel
    wph
    @14
    @10
    @15
    adantr
    #
    cS
    cV
    cW
    islshpcv.v
    islshpcv.s
    lss1
    syl
    #
    wph
    @0
    @9
    simprr
    #
    lcvpss
    pssned
    @23
    @6
    cC
    @3
    cS
    cU
    cV
    cW
    vq
    islshpcv.s
    @11
    @12
    islshpcv.c
    @25
    @24
    @26
    @27
    lcvat
    3jca
    ex
    impbid
    bitrd
end
