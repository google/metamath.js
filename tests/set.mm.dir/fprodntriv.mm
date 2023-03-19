include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "cuz.mm"
include "cfv.mm"
include "syl6eleq.mm"
include "peano2uz.mm"
include "syl.mm"
include "syl6eleqr.mm"
include "ax-1ne0.mm"
include "cvv.mm"
include "eqid.mm"
include "cz.mm"
include "eluzelz.mm"
include "eleq2s.mm"
include "peano2zd.mm"
include "seqex.mm"
include "a1i.mm"
include "1cnd.mm"
include "csn.mm"
include "cxp.mm"
include "simpr.mm"
include "cfz.mm"
include "csb.mm"
include "wss.mm"
include "ad2antrr.mm"
include "w3a.mm"
include "cle.mm"
include "clt.mm"
include "wn.mm"
include "zred.mm"
include "elfzelz.mm"
include "adantl.mm"
include "ltp1d.mm"
include "elfzle1.mm"
include "ltletrd.mm"
include "ltnled.mm"
include "mpbid.mm"
include "intnand.mm"
include "elfz2.mm"
include "sylnibr.mm"
include "ssneldd.mm"
include "iffalsed.mm"
include "cc.mm"
include "wceq.mm"
include "fzssuz.mm"
include "adantr.mm"
include "uzss.mm"
include "syl6sseqr.mm"
include "syl5ss.mm"
include "sselda.mm"
include "ax-1cn.mm"
include "syl6eqel.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfif.mm"
include "weq.mm"
include "eleq1.mm"
include "csbeq1a.mm"
include "ifbieq1d.mm"
include "fvmptf.mm"
include "syl2anc.mm"
include "elfzuz.mm"
include "1ex.mm"
include "fvconst2.mm"
include "3eqtr4d.mm"
include "seqfveq.mm"
include "prodf1.mm"
include "eqtrd.mm"
include "climconst.mm"
include "neeq1.mm"
include "breq2.mm"
include "anbi12d.mm"
include "spcev.mm"
include "sylancr.mm"
include "seqeq1.mm"
include "breq1d.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "rspcev.mm"

theorem fprodntriv
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vm: setvar m
  assume fprodntriv.1: |- Z = ( ZZ>= ` M )
  assume fprodntriv.2: |- ( ph -> N e. Z )
  assume fprodntriv.3: |- ( ph -> A C_ ( M ... N ) )

  disjoint A k
  disjoint A n
  disjoint A y
  disjoint B n
  disjoint B y
  disjoint k n
  disjoint k y
  disjoint N n
  disjoint n ph
  disjoint n y
  disjoint N y
  disjoint Z k
  disjoint Z n
  disjoint Z y
  disjoint A m
  disjoint B m
  disjoint k m
  disjoint m n
  disjoint m ph
  disjoint N m
  disjoint Z m
  assert |- ( ph -> E. n e. Z E. y ( y =/= 0 /\ seq n ( x. , ( k e. Z |-> if ( k e. A , B , 1 ) ) ) ~~> y ) )

  proof
    wph
    cN
    c1
    caddc
    co
    #
    cZ
    wcel
    vy
    cv
    #
    cc0
    wne
    #
    cmul
    vk
    cZ
    vk
    cv
    #
    cA
    wcel
    #
    cB
    c1
    cif
    #
    cmpt
    #
    @0
    cseq
    #
    @1
    cli
    wbr
    #
    wa
    #
    vy
    wex
    #
    @2
    cmul
    @6
    vn
    cv
    #
    cseq
    #
    @1
    cli
    wbr
    #
    wa
    #
    vy
    wex
    #
    vn
    cZ
    wrex
    wph
    @0
    cM
    cuz
    cfv
    #
    cZ
    wph
    cN
    @16
    wcel
    @0
    @16
    wcel
    #
    wph
    cN
    cZ
    @16
    fprodntriv.2
    fprodntriv.1
    syl6eleq
    cM
    cN
    peano2uz
    syl
    #
    fprodntriv.1
    syl6eleqr
    wph
    c1
    cc0
    wne
    #
    @7
    c1
    cli
    wbr
    #
    @10
    ax-1ne0
    wph
    c1
    vn
    @7
    @0
    cvv
    @0
    cuz
    cfv
    #
    @21
    eqid
    #
    wph
    cN
    wph
    cN
    cZ
    wcel
    cN
    cz
    wcel
    #
    fprodntriv.2
    @23
    cN
    @16
    cZ
    cM
    cN
    eluzelz
    fprodntriv.1
    eleq2s
    syl
    #
    peano2zd
    @7
    cvv
    wcel
    wph
    cmul
    @6
    @0
    seqex
    a1i
    wph
    1cnd
    wph
    @11
    @21
    wcel
    #
    wa
    #
    @11
    @7
    cfv
    @11
    cmul
    @21
    c1
    csn
    cxp
    #
    @0
    cseq
    cfv
    #
    c1
    @26
    cmul
    vm
    @6
    @27
    @0
    @11
    wph
    @25
    simpr
    @26
    vm
    cv
    #
    @0
    @11
    cfz
    co
    #
    wcel
    #
    wa
    #
    @29
    cA
    wcel
    #
    vk
    @29
    cB
    csb
    #
    c1
    cif
    #
    c1
    @29
    @6
    cfv
    #
    @29
    @27
    cfv
    #
    @32
    @33
    @34
    c1
    @32
    cA
    cM
    cN
    cfz
    co
    #
    @29
    wph
    cA
    @38
    wss
    @25
    @31
    fprodntriv.3
    ad2antrr
    @32
    cM
    cz
    wcel
    @23
    @29
    cz
    wcel
    #
    w3a
    #
    cM
    @29
    cle
    wbr
    #
    @29
    cN
    cle
    wbr
    #
    wa
    #
    wa
    @29
    @38
    wcel
    @32
    @43
    @40
    @32
    @42
    @41
    @32
    cN
    @29
    clt
    wbr
    @42
    wn
    @32
    cN
    @0
    @29
    @32
    cN
    wph
    @23
    @25
    @31
    @24
    ad2antrr
    #
    zred
    #
    @32
    @0
    @32
    cN
    @44
    peano2zd
    zred
    @32
    @29
    @31
    @39
    @26
    @29
    @0
    @11
    elfzelz
    adantl
    zred
    #
    @32
    cN
    @45
    ltp1d
    @31
    @0
    @29
    cle
    wbr
    @26
    @29
    @0
    @11
    elfzle1
    adantl
    ltletrd
    @32
    cN
    @29
    @45
    @46
    ltnled
    mpbid
    intnand
    intnand
    @29
    cM
    cN
    elfz2
    sylnibr
    ssneldd
    iffalsed
    #
    @32
    @29
    cZ
    wcel
    @35
    cc
    wcel
    @36
    @35
    wceq
    @26
    @30
    cZ
    @29
    @26
    @30
    @21
    cZ
    @0
    @11
    fzssuz
    @26
    @21
    @16
    cZ
    @26
    @17
    @21
    @16
    wss
    wph
    @17
    @25
    @18
    adantr
    cM
    @0
    uzss
    syl
    fprodntriv.1
    syl6sseqr
    syl5ss
    sselda
    @32
    @35
    c1
    cc
    @47
    ax-1cn
    syl6eqel
    vk
    @29
    @5
    @35
    cZ
    @6
    cc
    vk
    @29
    nfcv
    @33
    vk
    @34
    c1
    @33
    vk
    nfv
    vk
    @29
    cB
    nfcsb1v
    vk
    c1
    nfcv
    nfif
    vk
    vm
    weq
    @4
    @33
    cB
    @34
    c1
    @3
    @29
    cA
    eleq1
    vk
    @29
    cB
    csbeq1a
    ifbieq1d
    @6
    eqid
    fvmptf
    syl2anc
    @32
    @29
    @21
    wcel
    #
    @37
    c1
    wceq
    @31
    @48
    @26
    @29
    @0
    @11
    elfzuz
    adantl
    @21
    c1
    @29
    1ex
    fvconst2
    syl
    3eqtr4d
    seqfveq
    @25
    @28
    c1
    wceq
    wph
    @0
    @11
    @21
    @22
    prodf1
    adantl
    eqtrd
    climconst
    @9
    @19
    @20
    wa
    vy
    c1
    1ex
    @1
    c1
    wceq
    @2
    @19
    @8
    @20
    @1
    c1
    cc0
    neeq1
    @1
    c1
    @7
    cli
    breq2
    anbi12d
    spcev
    sylancr
    @15
    @10
    vn
    @0
    cZ
    @11
    @0
    wceq
    #
    @14
    @9
    vy
    @49
    @13
    @8
    @2
    @49
    @12
    @7
    @1
    cli
    cmul
    @6
    @11
    @0
    seqeq1
    breq1d
    anbi2d
    exbidv
    rspcev
    syl2anc
end
