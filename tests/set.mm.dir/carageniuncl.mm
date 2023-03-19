include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "cdm.mm"
include "cuni.mm"
include "eqid.mm"
include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "elssuni.mm"
include "syl.mm"
include "wceq.mm"
include "caragenuni.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "cvv.mm"
include "wb.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "iunex.mm"
include "a1i.mm"
include "elpwg.mm"
include "mpbird.mm"
include "cin.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cxr.mm"
include "iccssxr.mm"
include "come.mm"
include "elpwi.mm"
include "ssinss1.mm"
include "adantl.mm"
include "omecl.mm"
include "sseldi.mm"
include "ssdifssd.mm"
include "xaddcld.mm"
include "cle.mm"
include "wbr.mm"
include "pnfge.mm"
include "id.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "wn.mm"
include "cr.mm"
include "simpl.mm"
include "cico.mm"
include "rge0ssre.mm"
include "0xr.mm"
include "pnfxr.mm"
include "wne.mm"
include "necon3bi.mm"
include "eliccelicod.mm"
include "caddc.mm"
include "crp.mm"
include "cfzo.mm"
include "cmpt.mm"
include "cfz.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "cz.mm"
include "ad3antrrr.mm"
include "wf.mm"
include "fveq2.mm"
include "oveq2.mm"
include "iuneq1d.mm"
include "difeq12d.mm"
include "cbvmptv.mm"
include "carageniuncllem2.mm"
include "xralrple.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"
include "omelesplit.mm"
include "xrletrid.mm"
include "carageneld.mm"

theorem carageniuncl
  let wph: wff ph
  let cS: class S
  let vn: setvar n
  let cE: class E
  let cM: class M
  let cO: class O
  let cZ: class Z
  let va: setvar a
  let vi: setvar i
  let vx: setvar x
  let vm: setvar m
  let vk: setvar k
  assume carageniuncl.o: |- ( ph -> O e. OutMeas )
  assume carageniuncl.s: |- S = ( CaraGen ` O )
  assume carageniuncl.3: |- ( ph -> M e. ZZ )
  assume carageniuncl.z: |- Z = ( ZZ>= ` M )
  assume carageniuncl.e: |- ( ph -> E : Z --> S )

  disjoint E n
  disjoint M n
  disjoint O n
  disjoint Z n
  disjoint n ph
  disjoint E a
  disjoint E i
  disjoint E x
  disjoint a i
  disjoint a n
  disjoint a x
  disjoint i n
  disjoint i x
  disjoint n x
  disjoint E m
  disjoint i m
  disjoint m n
  disjoint M i
  disjoint M m
  disjoint O a
  disjoint O i
  disjoint O x
  disjoint S i
  disjoint Z a
  disjoint Z i
  disjoint Z x
  disjoint Z m
  disjoint a ph
  disjoint i ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> U_ n e. Z ( E ` n ) e. S )

  proof
    wph
    cS
    vn
    cZ
    vn
    cv
    #
    cE
    cfv
    #
    ciun
    #
    cO
    cO
    cdm
    cuni
    #
    va
    carageniuncl.o
    @3
    eqid
    #
    carageniuncl.s
    wph
    @2
    @3
    cpw
    #
    wcel
    #
    @2
    @3
    wss
    #
    wph
    @1
    @3
    wss
    #
    vn
    cZ
    wral
    @7
    wph
    @8
    vn
    cZ
    wph
    @0
    cZ
    wcel
    #
    wa
    #
    @1
    cS
    cuni
    #
    @3
    @10
    @1
    cS
    wcel
    @1
    @11
    wss
    wph
    cZ
    cS
    @0
    cE
    carageniuncl.e
    ffvelrnda
    @1
    cS
    elssuni
    syl
    wph
    @11
    @3
    wceq
    @9
    wph
    cS
    cO
    carageniuncl.o
    carageniuncl.s
    caragenuni
    adantr
    sseqtrd
    ralrimiva
    vn
    cZ
    @1
    @3
    iunss
    sylibr
    wph
    @2
    cvv
    wcel
    #
    @6
    @7
    wb
    @12
    wph
    vn
    cZ
    @1
    cZ
    cM
    cuz
    cfv
    cvv
    carageniuncl.z
    cM
    cuz
    fvex
    eqeltri
    @0
    cE
    fvex
    iunex
    a1i
    @2
    @3
    cvv
    elpwg
    syl
    mpbird
    wph
    va
    cv
    #
    @5
    wcel
    #
    wa
    #
    @13
    @2
    cin
    #
    cO
    cfv
    #
    @13
    @2
    cdif
    #
    cO
    cfv
    #
    cxad
    co
    #
    @13
    cO
    cfv
    #
    @15
    @17
    @19
    @15
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @17
    cc0
    cpnf
    iccssxr
    #
    @15
    @16
    cO
    @3
    wph
    cO
    come
    wcel
    #
    @14
    carageniuncl.o
    adantr
    #
    @4
    @14
    @16
    @3
    wss
    #
    wph
    @14
    @13
    @3
    wss
    #
    @26
    @13
    @3
    elpwi
    #
    @13
    @2
    @3
    ssinss1
    syl
    adantl
    omecl
    sseldi
    @15
    @22
    cxr
    @19
    @23
    @15
    @18
    cO
    @3
    @25
    @4
    @15
    @13
    @3
    @2
    @14
    @27
    wph
    @28
    adantl
    #
    ssdifssd
    omecl
    sseldi
    xaddcld
    #
    @15
    @22
    cxr
    @21
    @23
    @15
    @13
    cO
    @3
    @25
    @4
    @29
    omecl
    #
    sseldi
    @15
    @21
    cpnf
    wceq
    #
    @20
    @21
    cle
    wbr
    #
    @15
    @32
    wa
    @20
    cpnf
    @21
    cle
    @15
    @20
    cpnf
    cle
    wbr
    #
    @32
    @15
    @20
    cxr
    wcel
    #
    @34
    @30
    @20
    pnfge
    syl
    adantr
    @32
    cpnf
    @21
    wceq
    @15
    @32
    @21
    cpnf
    @32
    id
    #
    eqcomd
    adantl
    breqtrd
    @15
    @32
    wn
    #
    wa
    #
    @15
    @21
    cr
    wcel
    #
    @33
    @15
    @37
    simpl
    #
    @38
    cc0
    cpnf
    cico
    co
    cr
    @21
    rge0ssre
    @38
    cc0
    cpnf
    @21
    cc0
    cxr
    wcel
    @38
    0xr
    a1i
    cpnf
    cxr
    wcel
    @38
    pnfxr
    a1i
    @38
    @15
    @21
    @22
    wcel
    @40
    @31
    syl
    @37
    @21
    cpnf
    wne
    @15
    @32
    @21
    cpnf
    @36
    necon3bi
    adantl
    eliccelicod
    sseldi
    @15
    @39
    wa
    #
    @33
    @20
    @21
    vx
    cv
    #
    caddc
    co
    cle
    wbr
    #
    vx
    crp
    wral
    #
    @41
    @43
    vx
    crp
    @41
    @42
    crp
    wcel
    #
    wa
    @13
    cS
    vi
    vn
    cE
    vm
    cZ
    vm
    cv
    #
    cE
    cfv
    #
    vi
    cM
    @46
    cfzo
    co
    #
    vi
    cv
    cE
    cfv
    #
    ciun
    #
    cdif
    #
    cmpt
    vn
    cZ
    vi
    cM
    @0
    cfz
    co
    @49
    ciun
    cmpt
    #
    cM
    cO
    @3
    @42
    cZ
    @15
    @24
    @39
    @45
    @25
    ad2antrr
    carageniuncl.s
    @4
    @15
    @27
    @39
    @45
    @29
    ad2antrr
    @41
    @39
    @45
    @15
    @39
    simpr
    #
    adantr
    wph
    cM
    cz
    wcel
    @14
    @39
    @45
    carageniuncl.3
    ad3antrrr
    carageniuncl.z
    wph
    cZ
    cS
    cE
    wf
    @14
    @39
    @45
    carageniuncl.e
    ad3antrrr
    @41
    @45
    simpr
    @52
    eqid
    vm
    vn
    cZ
    @51
    @1
    vi
    cM
    @0
    cfzo
    co
    #
    @49
    ciun
    #
    cdif
    @46
    @0
    wceq
    #
    @47
    @1
    @50
    @55
    @46
    @0
    cE
    fveq2
    @56
    vi
    @48
    @54
    @49
    @46
    @0
    cM
    cfzo
    oveq2
    iuneq1d
    difeq12d
    cbvmptv
    carageniuncllem2
    ralrimiva
    @41
    @35
    @39
    @33
    @44
    wb
    @15
    @35
    @39
    @30
    adantr
    @53
    vx
    @20
    @21
    xralrple
    syl2anc
    mpbird
    syl2anc
    pm2.61dan
    @15
    @13
    @2
    cO
    @3
    @25
    @4
    @29
    omelesplit
    xrletrid
    carageneld
end
