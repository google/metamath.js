include "cv.mm"
include "cfv.mm"
include "cneg.mm"
include "cmpt.mm"
include "clsp.mm"
include "csmblfn.mm"
include "clsi.mm"
include "wceq.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "cxne.mm"
include "cdm.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "ciin.mm"
include "ciun.mm"
include "cr.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "id.mm"
include "sseldi.mm"
include "eqid.mm"
include "allbutfi.mm"
include "sylib.mm"
include "adantl.mm"
include "wi.mm"
include "cvv.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "fvexi.mm"
include "eluzelz2.mm"
include "zred.mm"
include "ad2antlr.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cin.mm"
include "wf.mm"
include "simpll.mm"
include "elinel1.mm"
include "csalg.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "smff.mm"
include "syl2an.mm"
include "simplr.mm"
include "cz.mm"
include "eluzelz2d.mm"
include "cxr.mm"
include "rexrd.mm"
include "pnfxr.mm"
include "elinel2.mm"
include "icogelbd.mm"
include "eluzd.mm"
include "adantlr.mm"
include "rspa.mm"
include "syl2anc.mm"
include "adantlll.mm"
include "ffvelrnd.mm"
include "liminfval4.mm"
include "rexlimdva2.mm"
include "mpd.mm"
include "xnegeqd.mm"
include "mptex.mm"
include "limsupcli.mm"
include "xnegnegi.mm"
include "eqtr2d.mm"
include "rabeq2i.mm"
include "simprbi.mm"
include "rexnegd.mm"
include "renegcld.mm"
include "eqeltrrd.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "c0.mm"
include "wne.mm"
include "uzn0d.mm"
include "fvex.mm"
include "dmex.mm"
include "rgenw.mm"
include "iinexg.mm"
include "rgen.mm"
include "iunexg.mm"
include "mp2an.mm"
include "ssexi.mm"
include "wb.mm"
include "biimpi.mm"
include "imp.mm"
include "sylan2.mm"
include "simpl.mm"
include "simpr.mm"
include "xnegrecl2.mm"
include "xnegrecl.mm"
include "eqeltrd.mm"
include "impbida.mm"
include "syl.mm"
include "rabbidva.mm"
include "mpteq1df.mm"
include "w3a.mm"
include "negex.mm"
include "feqmptd.mm"
include "smfneg.mm"
include "smflimsupmpt.mm"

theorem smfliminflem
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cS: class S
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  assume smfliminflem.m: |- ( ph -> M e. ZZ )
  assume smfliminflem.z: |- Z = ( ZZ>= ` M )
  assume smfliminflem.s: |- ( ph -> S e. SAlg )
  assume smfliminflem.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smfliminflem.d: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( liminf ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) e. RR }
  assume smfliminflem.g: |- G = ( x e. D |-> ( liminf ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) )

  disjoint D x
  disjoint F n
  disjoint F x
  disjoint n x
  disjoint M m
  disjoint S m
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint m n
  disjoint m x
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> G e. ( SMblFn ` S ) )

  proof
    wph
    cG
    vx
    cD
    vm
    cZ
    vx
    cv
    #
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cneg
    #
    cmpt
    #
    clsp
    cfv
    #
    cneg
    #
    cmpt
    #
    cS
    csmblfn
    cfv
    #
    wph
    cG
    vx
    cD
    vm
    cZ
    @3
    cmpt
    clsi
    cfv
    #
    cmpt
    #
    @8
    cG
    @11
    wceq
    wph
    smfliminflem.g
    a1i
    wph
    vx
    cD
    @10
    @7
    wph
    @0
    cD
    wcel
    #
    wa
    #
    @10
    @6
    cxne
    #
    @7
    @13
    @0
    @2
    cdm
    #
    wcel
    #
    vm
    vn
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vn
    cZ
    wrex
    #
    @10
    @14
    wceq
    #
    @12
    @20
    wph
    @12
    @0
    vn
    cZ
    vm
    @18
    @15
    ciin
    #
    ciun
    #
    wcel
    #
    @20
    @12
    cD
    @23
    @0
    cD
    @10
    cr
    wcel
    #
    vx
    @23
    crab
    #
    @23
    smfliminflem.d
    @25
    vx
    @23
    ssrab2
    eqsstri
    #
    @12
    id
    sseldi
    @23
    @15
    vm
    vn
    cM
    @0
    cZ
    smfliminflem.z
    @23
    eqid
    allbutfi
    #
    sylib
    adantl
    wph
    @20
    @21
    wi
    @12
    wph
    @19
    @21
    vn
    cZ
    wph
    @17
    cZ
    wcel
    #
    wa
    #
    @19
    wa
    #
    vm
    cZ
    @3
    @17
    cvv
    @30
    @19
    vm
    @30
    vm
    nfv
    @16
    vm
    @18
    nfra1
    nfan
    cZ
    cvv
    wcel
    #
    @31
    cZ
    cM
    cuz
    smfliminflem.z
    fvexi
    #
    a1i
    @29
    @17
    cr
    wcel
    wph
    @19
    @29
    @17
    cM
    @17
    cZ
    smfliminflem.z
    eluzelz2
    #
    zred
    #
    ad2antlr
    @31
    @1
    cZ
    @17
    cpnf
    cico
    co
    #
    cin
    wcel
    #
    wa
    @15
    cr
    @0
    @2
    @31
    wph
    @1
    cZ
    wcel
    #
    @15
    cr
    @2
    wf
    @37
    wph
    @29
    @19
    simpll
    @1
    cZ
    @36
    elinel1
    #
    wph
    @38
    wa
    #
    @15
    cS
    @2
    wph
    cS
    csalg
    wcel
    @38
    smfliminflem.s
    adantr
    #
    wph
    cZ
    @9
    @1
    cF
    smfliminflem.f
    ffvelrnda
    #
    @15
    eqid
    smff
    #
    syl2an
    @29
    @19
    @37
    @16
    wph
    @29
    @19
    wa
    @37
    wa
    @19
    @1
    @18
    wcel
    #
    @16
    @29
    @19
    @37
    simplr
    @29
    @37
    @44
    @19
    @29
    @37
    wa
    #
    @17
    @1
    @18
    @18
    eqid
    #
    @29
    @17
    cz
    wcel
    @37
    @34
    adantr
    @37
    @1
    cz
    wcel
    @29
    @37
    cM
    @1
    cZ
    smfliminflem.z
    @39
    eluzelz2d
    adantl
    @45
    @17
    cpnf
    @1
    @29
    @17
    cxr
    wcel
    @37
    @29
    @17
    @35
    rexrd
    adantr
    cpnf
    cxr
    wcel
    @45
    pnfxr
    a1i
    @37
    @1
    @36
    wcel
    @29
    @1
    cZ
    @36
    elinel2
    adantl
    icogelbd
    eluzd
    adantlr
    @16
    vm
    @18
    rspa
    syl2anc
    adantlll
    ffvelrnd
    liminfval4
    rexlimdva2
    #
    adantr
    mpd
    #
    @13
    @6
    @13
    @10
    cneg
    #
    @6
    cr
    @13
    @6
    @10
    cxne
    #
    @49
    @13
    @50
    @14
    cxne
    #
    @6
    @13
    @10
    @14
    @48
    xnegeqd
    @51
    @6
    wceq
    @13
    @6
    @5
    cvv
    vm
    cZ
    @4
    @33
    mptex
    limsupcli
    #
    xnegnegi
    a1i
    eqtr2d
    @13
    @10
    @12
    @25
    wph
    @12
    @24
    @25
    @25
    vx
    cD
    @23
    smfliminflem.d
    rabeq2i
    simprbi
    adantl
    #
    rexnegd
    eqtr2d
    @13
    @10
    @53
    renegcld
    eqeltrrd
    #
    rexnegd
    eqtrd
    mpteq2dva
    eqtrd
    wph
    vx
    cD
    @6
    cS
    cvv
    wph
    vx
    nfv
    #
    smfliminflem.s
    cD
    cvv
    wcel
    wph
    cD
    @23
    @32
    @22
    cvv
    wcel
    #
    vn
    cZ
    wral
    @23
    cvv
    wcel
    @33
    @56
    vn
    cZ
    @29
    @18
    c0
    wne
    @15
    cvv
    wcel
    #
    vm
    @18
    wral
    #
    @56
    @29
    @17
    @18
    @34
    @46
    uzn0d
    @58
    @29
    @57
    vm
    @18
    @2
    @1
    cF
    fvex
    dmex
    #
    rgenw
    a1i
    vm
    @18
    @15
    cvv
    iinexg
    syl2anc
    rgen
    vn
    cZ
    @22
    cvv
    cvv
    iunexg
    mp2an
    @27
    ssexi
    a1i
    @54
    wph
    vx
    cD
    @6
    cmpt
    vx
    @6
    cr
    wcel
    #
    vx
    @23
    crab
    #
    @6
    cmpt
    #
    @9
    wph
    vx
    cD
    @61
    @6
    @55
    wph
    cD
    @26
    @61
    cD
    @26
    wceq
    wph
    smfliminflem.d
    a1i
    wph
    @25
    @60
    vx
    @23
    wph
    @24
    wa
    @21
    @25
    @60
    wb
    @24
    wph
    @20
    @21
    @24
    @20
    @28
    biimpi
    wph
    @20
    @21
    @47
    imp
    sylan2
    @21
    @25
    @60
    @21
    @25
    wa
    #
    @6
    cxr
    wcel
    #
    @14
    cr
    wcel
    #
    @60
    @64
    @63
    @52
    a1i
    @63
    @10
    @14
    cr
    @21
    @25
    simpl
    @21
    @25
    simpr
    eqeltrrd
    @6
    xnegrecl2
    syl2anc
    @21
    @60
    wa
    @10
    @14
    cr
    @21
    @60
    simpl
    @60
    @65
    @21
    @6
    xnegrecl
    adantl
    eqeltrd
    impbida
    syl
    rabbidva
    eqtrd
    mpteq1df
    wph
    vx
    @15
    @4
    @61
    cS
    vm
    vn
    @62
    cM
    cvv
    cZ
    wph
    vm
    nfv
    @55
    wph
    vn
    nfv
    smfliminflem.m
    smfliminflem.z
    smfliminflem.s
    @4
    cvv
    wcel
    wph
    @38
    @16
    w3a
    @3
    negex
    a1i
    @40
    vx
    @15
    @3
    cS
    cvv
    @40
    vx
    nfv
    @41
    @57
    @40
    @59
    a1i
    @40
    @15
    cr
    @0
    @2
    @43
    ffvelrnda
    @40
    @2
    vx
    @15
    @3
    cmpt
    @9
    @40
    vx
    @15
    cr
    @2
    @43
    feqmptd
    @42
    eqeltrrd
    smfneg
    @61
    eqid
    @62
    eqid
    smflimsupmpt
    eqeltrd
    smfneg
    eqeltrd
end
