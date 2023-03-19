include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "ccn.mm"
include "cc.mm"
include "ccncf.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "ccnp.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cuni.mm"
include "sselda.mm"
include "eluni2.mm"
include "sylib.mm"
include "w3a.mm"
include "cin.mm"
include "simp1l.mm"
include "simp2.mm"
include "elin.mm"
include "biimpri.mm"
include "adantll.mm"
include "3adant2.mm"
include "cres.mm"
include "wb.mm"
include "cdm.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "ineq2d.mm"
include "incom.mm"
include "syl6req.mm"
include "reseq2d.mm"
include "wrel.mm"
include "frel.mm"
include "resindm.mm"
include "eqtrd.mm"
include "wss.mm"
include "inss1.mm"
include "a1i.mm"
include "sstrd.mm"
include "ssid.mm"
include "eqid.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "unicntop.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "eleq12d.mm"
include "adantr.mm"
include "mpbird.mm"
include "3adant3.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "3ad2ant1.mm"
include "cncnp.mm"
include "mpbid.mm"
include "simprd.mm"
include "simp3.mm"
include "rspa.mm"
include "cvv.mm"
include "cnex.mm"
include "ssex.mm"
include "restabs.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "fveq1d.mm"
include "eleqtrd.mm"
include "cnt.mm"
include "resttop.mm"
include "restuni.mm"
include "sseqtrd.mm"
include "isopn3.mm"
include "feq2d.mm"
include "cnprest.mm"
include "syl22anc.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "mpbir2and.mm"

theorem cncfuni
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let vb: setvar b
  let vx: setvar x
  let vk: setvar k
  assume cncfuni.acn: |- ( ph -> A C_ CC )
  assume cncfuni.f: |- ( ph -> F : A --> CC )
  assume cncfuni.auni: |- ( ph -> A C_ U. B )
  assume cncfuni.opn: |- ( ( ph /\ b e. B ) -> ( A i^i b ) e. ( ( TopOpen ` CCfld ) |`t A ) )
  assume cncfuni.fcn: |- ( ( ph /\ b e. B ) -> ( F |` b ) e. ( ( A i^i b ) -cn-> CC ) )

  disjoint A b
  disjoint B b
  disjoint F b
  disjoint b ph
  disjoint A x
  disjoint b x
  disjoint F x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> F e. ( A -cn-> CC ) )

  proof
    wph
    cF
    ccnfld
    ctopn
    cfv
    #
    cA
    crest
    co
    #
    @0
    ccn
    co
    #
    cA
    cc
    ccncf
    co
    #
    wph
    cF
    @2
    wcel
    #
    cA
    cc
    cF
    wf
    #
    cF
    vx
    cv
    #
    @1
    @0
    ccnp
    co
    cfv
    wcel
    #
    vx
    cA
    wral
    #
    cncfuni.f
    wph
    @7
    vx
    cA
    wph
    @6
    cA
    wcel
    #
    wa
    #
    @6
    vb
    cv
    #
    wcel
    #
    vb
    cB
    wrex
    #
    @7
    @10
    @6
    cB
    cuni
    #
    wcel
    @13
    wph
    cA
    @14
    @6
    cncfuni.auni
    sselda
    vb
    @6
    cB
    eluni2
    sylib
    @10
    @12
    @7
    vb
    cB
    @10
    @11
    cB
    wcel
    #
    @12
    w3a
    wph
    @15
    @6
    cA
    @11
    cin
    #
    wcel
    #
    @7
    wph
    @9
    @15
    @12
    simp1l
    @10
    @15
    @12
    simp2
    @10
    @12
    @17
    @15
    @9
    @12
    @17
    wph
    @17
    @9
    @12
    wa
    @6
    cA
    @11
    elin
    biimpri
    adantll
    3adant2
    wph
    @15
    @17
    w3a
    #
    @7
    cF
    @16
    cres
    #
    @6
    @1
    @16
    crest
    co
    #
    @0
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    @18
    @19
    @6
    @0
    @16
    crest
    co
    #
    @0
    ccnp
    co
    #
    cfv
    #
    @22
    @18
    @19
    @26
    wcel
    #
    vx
    @16
    wral
    #
    @17
    @27
    @18
    @16
    cc
    @19
    wf
    #
    @28
    @18
    @19
    @24
    @0
    ccn
    co
    #
    wcel
    #
    @29
    @28
    wa
    #
    wph
    @15
    @31
    @17
    wph
    @15
    wa
    @31
    cF
    @11
    cres
    #
    @16
    cc
    ccncf
    co
    #
    wcel
    #
    cncfuni.fcn
    wph
    @31
    @35
    wb
    @15
    wph
    @19
    @33
    @30
    @34
    wph
    @19
    cF
    @11
    cF
    cdm
    #
    cin
    #
    cres
    #
    @33
    wph
    @16
    @37
    cF
    wph
    @37
    @11
    cA
    cin
    @16
    wph
    @36
    cA
    @11
    wph
    @5
    @36
    cA
    wceq
    cncfuni.f
    cA
    cc
    cF
    fdm
    syl
    ineq2d
    @11
    cA
    incom
    syl6req
    reseq2d
    wph
    cF
    wrel
    #
    @38
    @33
    wceq
    wph
    @5
    @39
    cncfuni.f
    cA
    cc
    cF
    frel
    syl
    cF
    @11
    resindm
    syl
    eqtrd
    wph
    @34
    @30
    wph
    @16
    cc
    wss
    #
    cc
    cc
    wss
    #
    @34
    @30
    wceq
    wph
    @16
    cA
    cc
    @16
    cA
    wss
    #
    wph
    cA
    @11
    inss1
    a1i
    #
    cncfuni.acn
    sstrd
    #
    @41
    wph
    cc
    ssid
    a1i
    #
    @16
    cc
    @0
    @24
    @0
    @0
    eqid
    #
    @24
    eqid
    @0
    cc
    crest
    co
    #
    @0
    @0
    ctop
    wcel
    #
    @47
    @0
    wceq
    @0
    @46
    cnfldtop
    #
    @0
    ctop
    cc
    unicntop
    restid
    ax-mp
    eqcomi
    #
    cncfcn
    syl2anc
    eqcomd
    eleq12d
    adantr
    mpbird
    3adant3
    @18
    @24
    @16
    ctopon
    cfv
    wcel
    #
    @0
    cc
    ctopon
    cfv
    wcel
    #
    @31
    @32
    wb
    wph
    @15
    @51
    @17
    wph
    @52
    @40
    @51
    @52
    wph
    @0
    @46
    cnfldtopon
    #
    a1i
    #
    @44
    @16
    @0
    cc
    resttopon
    syl2anc
    3ad2ant1
    @52
    @18
    @53
    a1i
    vx
    @19
    @24
    @0
    @16
    cc
    cncnp
    syl2anc
    mpbid
    simprd
    wph
    @15
    @17
    simp3
    #
    @27
    vx
    @16
    rspa
    syl2anc
    wph
    @15
    @26
    @22
    wceq
    @17
    wph
    @6
    @25
    @21
    wph
    @24
    @20
    @0
    ccnp
    wph
    @20
    @24
    wph
    @48
    @42
    cA
    cvv
    wcel
    #
    @20
    @24
    wceq
    @48
    wph
    @49
    a1i
    #
    @43
    wph
    cA
    cc
    wss
    #
    @56
    cncfuni.acn
    cA
    cc
    cnex
    ssex
    syl
    #
    @16
    cA
    @0
    ctop
    cvv
    restabs
    syl3anc
    eqcomd
    oveq1d
    fveq1d
    3ad2ant1
    eleqtrd
    @18
    @1
    ctop
    wcel
    #
    @16
    @1
    cuni
    #
    wss
    #
    @6
    @16
    @1
    cnt
    cfv
    cfv
    #
    wcel
    @61
    cc
    cF
    wf
    #
    @7
    @23
    wb
    wph
    @15
    @60
    @17
    wph
    @48
    @56
    @60
    @57
    @59
    cA
    @0
    cvv
    resttop
    syl2anc
    3ad2ant1
    #
    wph
    @15
    @62
    @17
    wph
    @16
    cA
    @61
    @43
    wph
    @48
    @58
    cA
    @61
    wceq
    @57
    cncfuni.acn
    cA
    @0
    cc
    unicntop
    restuni
    syl2anc
    #
    sseqtrd
    3ad2ant1
    #
    @18
    @6
    @16
    @63
    @55
    @18
    @63
    @16
    @18
    @16
    @1
    wcel
    #
    @63
    @16
    wceq
    #
    wph
    @15
    @68
    @17
    cncfuni.opn
    3adant3
    @18
    @60
    @62
    @68
    @69
    wb
    @65
    @67
    @16
    @1
    @61
    @61
    eqid
    #
    isopn3
    syl2anc
    mpbid
    eqcomd
    eleqtrd
    wph
    @15
    @64
    @17
    wph
    @5
    @64
    cncfuni.f
    wph
    cA
    @61
    cc
    cF
    @66
    feq2d
    mpbid
    3ad2ant1
    @16
    @6
    cF
    @1
    @0
    @61
    cc
    @70
    unicntop
    cnprest
    syl22anc
    mpbird
    syl3anc
    rexlimdv3a
    mpd
    ralrimiva
    wph
    @1
    cA
    ctopon
    cfv
    wcel
    #
    @52
    @4
    @5
    @8
    wa
    wb
    wph
    @52
    @58
    @71
    @54
    cncfuni.acn
    cA
    @0
    cc
    resttopon
    syl2anc
    @54
    vx
    cF
    @1
    @0
    cA
    cc
    cncnp
    syl2anc
    mpbir2and
    wph
    @3
    @2
    wph
    @58
    @41
    @3
    @2
    wceq
    cncfuni.acn
    @45
    cA
    cc
    @0
    @1
    @0
    @46
    @1
    eqid
    @50
    cncfcn
    syl2anc
    eqcomd
    eleqtrd
end
