include "cdm.mm"
include "cin.mm"
include "cres.mm"
include "nfv.mm"
include "cuni.mm"
include "inss2.mm"
include "eqid.mm"
include "smfdmss.mm"
include "syl5ss.mm"
include "cr.mm"
include "wf.mm"
include "wss.mm"
include "smff.mm"
include "a1i.mm"
include "fssres.mm"
include "syl2anc.mm"
include "wrel.mm"
include "wceq.mm"
include "freld.mm"
include "resindm.mm"
include "syl.mm"
include "eqcomd.mm"
include "dmres.mm"
include "feq12d.mm"
include "mpbird.mm"
include "feq2d.mm"
include "mpbid.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "wrex.mm"
include "crest.mm"
include "co.mm"
include "csalg.mm"
include "adantr.mm"
include "csmblfn.mm"
include "simpr.mm"
include "smfpreimalt.mm"
include "wb.mm"
include "cvv.mm"
include "dmexd.mm"
include "elrest.mm"
include "w3a.mm"
include "elinel1.mm"
include "fvresd.mm"
include "breq1d.mm"
include "rabbiia.mm"
include "rabss2.mm"
include "ax-mp.mm"
include "id.mm"
include "inss1.mm"
include "eqsstrd.mm"
include "ssrab2.mm"
include "ssind.mm"
include "wral.mm"
include "nfrab1.mm"
include "nfcv.mm"
include "nfeq.mm"
include "elinel2.mm"
include "adantl.mm"
include "sseli.mm"
include "elind.mm"
include "eleqtrd.mm"
include "rabid.mm"
include "biimpi.mm"
include "simprd.mm"
include "jca.mm"
include "sylibr.mm"
include "ex.mm"
include "ralrimi.mm"
include "dfss3f.mm"
include "sseld.mm"
include "eqssd.mm"
include "eqtrd.mm"
include "3adant2.mm"
include "3ad2ant1.mm"
include "simp1l.mm"
include "ssexd.mm"
include "simp2.mm"
include "elrestd.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "issmfd.mm"

theorem sssmf
  let wph: wff ph
  let cB: class B
  let cS: class S
  let cF: class F
  let va: setvar a
  let vw: setvar w
  let vx: setvar x
  let vk: setvar k
  assume sssmf.s: |- ( ph -> S e. SAlg )
  assume sssmf.f: |- ( ph -> F e. ( SMblFn ` S ) )


  assert |- ( ph -> ( F |` B ) e. ( SMblFn ` S ) )

  proof
    wph
    vx
    cB
    cF
    cdm
    #
    cin
    #
    cS
    cF
    cB
    cres
    #
    va
    wph
    va
    nfv
    sssmf.s
    wph
    @1
    @0
    cS
    cuni
    cB
    @0
    inss2
    #
    wph
    @0
    cS
    cF
    sssmf.s
    sssmf.f
    @0
    eqid
    #
    smfdmss
    syl5ss
    wph
    @2
    cdm
    #
    cr
    @2
    wf
    #
    @1
    cr
    @2
    wf
    wph
    @6
    @1
    cr
    cF
    @1
    cres
    #
    wf
    #
    wph
    @0
    cr
    cF
    wf
    @1
    @0
    wss
    #
    @8
    wph
    @0
    cS
    cF
    sssmf.s
    sssmf.f
    @4
    smff
    #
    @9
    wph
    @3
    a1i
    #
    @0
    cr
    @1
    cF
    fssres
    syl2anc
    wph
    @5
    @1
    cr
    @2
    @7
    wph
    @7
    @2
    wph
    cF
    wrel
    @7
    @2
    wceq
    wph
    @0
    cr
    cF
    @10
    freld
    cF
    cB
    resindm
    syl
    eqcomd
    @5
    @1
    wceq
    wph
    cF
    cB
    dmres
    a1i
    #
    feq12d
    mpbird
    wph
    @5
    @1
    cr
    @2
    @12
    feq2d
    mpbid
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    #
    vx
    cv
    #
    cF
    cfv
    #
    @13
    clt
    wbr
    #
    vx
    @0
    crab
    #
    vw
    cv
    #
    @0
    cin
    #
    wceq
    #
    vw
    cS
    wrex
    #
    @16
    @2
    cfv
    #
    @13
    clt
    wbr
    #
    vx
    @1
    crab
    #
    cS
    @1
    crest
    co
    #
    wcel
    #
    @15
    @19
    cS
    @0
    crest
    co
    wcel
    #
    @23
    @15
    vx
    @13
    @0
    cS
    cF
    wph
    cS
    csalg
    wcel
    #
    @14
    sssmf.s
    adantr
    #
    wph
    cF
    cS
    csmblfn
    cfv
    #
    wcel
    @14
    sssmf.f
    adantr
    @4
    wph
    @14
    simpr
    smfpreimalt
    wph
    @29
    @23
    wb
    #
    @14
    wph
    @30
    @0
    cvv
    wcel
    @33
    sssmf.s
    wph
    cF
    @32
    sssmf.f
    dmexd
    #
    vw
    @19
    @0
    cS
    csalg
    cvv
    elrest
    syl2anc
    adantr
    mpbid
    @15
    @22
    @28
    vw
    cS
    @15
    @20
    cS
    wcel
    #
    @22
    @28
    @15
    @35
    @22
    w3a
    #
    @26
    @20
    @1
    cin
    #
    @27
    @15
    @22
    @26
    @37
    wceq
    #
    @35
    @22
    @38
    @15
    @22
    @26
    @18
    vx
    @1
    crab
    #
    @37
    @26
    @39
    wceq
    @22
    @25
    @18
    vx
    @1
    @16
    @1
    wcel
    #
    @24
    @17
    @13
    clt
    @40
    @16
    cB
    cF
    @16
    cB
    @0
    elinel1
    fvresd
    breq1d
    rabbiia
    a1i
    @22
    @39
    @37
    @22
    @39
    @20
    @1
    @22
    @39
    @19
    @20
    @9
    @39
    @19
    wss
    @3
    @18
    vx
    @1
    @0
    rabss2
    ax-mp
    @22
    @19
    @21
    @20
    @22
    id
    #
    @21
    @20
    wss
    @22
    @20
    @0
    inss1
    a1i
    eqsstrd
    syl5ss
    @39
    @1
    wss
    @22
    @18
    vx
    @1
    ssrab2
    a1i
    ssind
    @22
    @16
    @39
    wcel
    #
    vx
    @37
    wral
    #
    @37
    @39
    wss
    #
    @22
    @42
    vx
    @37
    vx
    @19
    @21
    @18
    vx
    @0
    nfrab1
    vx
    @21
    nfcv
    nfeq
    #
    @22
    @37
    @39
    @16
    @22
    @43
    @44
    @22
    @42
    vx
    @37
    @45
    @22
    @16
    @37
    wcel
    #
    @42
    @22
    @46
    wa
    #
    @40
    @18
    wa
    @42
    @47
    @40
    @18
    @46
    @40
    @22
    @16
    @20
    @1
    elinel2
    #
    adantl
    @47
    @16
    @19
    wcel
    #
    @18
    @47
    @16
    @21
    @19
    @46
    @16
    @21
    wcel
    @22
    @46
    @20
    @0
    @16
    @16
    @20
    @1
    elinel1
    @46
    @40
    @16
    @0
    wcel
    #
    @48
    @1
    @0
    @16
    @3
    sseli
    syl
    elind
    adantl
    @22
    @21
    @19
    wceq
    @46
    @22
    @19
    @21
    @41
    eqcomd
    adantr
    eleqtrd
    @49
    @50
    @18
    @49
    @50
    @18
    wa
    @18
    vx
    @0
    rabid
    biimpi
    simprd
    syl
    jca
    @18
    vx
    @1
    rabid
    sylibr
    ex
    ralrimi
    vx
    @37
    @39
    vx
    @37
    nfcv
    @18
    vx
    @1
    nfrab1
    dfss3f
    #
    sylibr
    sseld
    ralrimi
    @51
    sylibr
    eqssd
    eqtrd
    adantl
    3adant2
    @36
    @37
    @1
    cS
    csalg
    cvv
    @20
    @15
    @35
    @30
    @22
    @31
    3ad2ant1
    @36
    wph
    @1
    cvv
    wcel
    wph
    @14
    @35
    @22
    simp1l
    wph
    @1
    @0
    cvv
    @34
    @11
    ssexd
    syl
    @15
    @35
    @22
    simp2
    @37
    eqid
    elrestd
    eqeltrd
    3exp
    rexlimdv
    mpd
    issmfd
end
