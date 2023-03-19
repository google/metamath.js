include "cmul.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "cv.mm"
include "cpc.mm"
include "cle.mm"
include "cprime.mm"
include "wral.mm"
include "wa.mm"
include "wn.mm"
include "csb.mm"
include "cif.mm"
include "cn0.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "weq.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "cbvral.mm"
include "sylib.mm"
include "csbeq1.mm"
include "rspcv.mm"
include "mpan9.mm"
include "nn0ge0d.mm"
include "0le0.mm"
include "breq2.mm"
include "ifboth.mm"
include "sylancl.mm"
include "cn.mm"
include "cexp.mm"
include "cmpt.mm"
include "nfcv.mm"
include "nfov.mm"
include "nfif.mm"
include "eleq1.mm"
include "id.mm"
include "oveq12d.mm"
include "ifbieq1d.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "adantr.mm"
include "simpr.mm"
include "cuz.mm"
include "pcmpt2.mm"
include "breqtrrd.mm"
include "ralrimiva.mm"
include "cq.mm"
include "wb.mm"
include "wf.mm"
include "pcmptcl.mm"
include "simprd.mm"
include "eluznn.mm"
include "syl2anc.mm"
include "ffvelrnd.mm"
include "nnzd.mm"
include "znq.mm"
include "pcz.mm"
include "syl.mm"
include "mpbird.mm"
include "wne.mm"
include "nnne0d.mm"
include "dvdsval2.mm"
include "syl3anc.mm"

theorem pcmptdvds
  let wph: wff ph
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let vp: setvar p
  let cB: class B
  let cP: class P
  assume pcmpt.1: |- F = ( n e. NN |-> if ( n e. Prime , ( n ^ A ) , 1 ) )
  assume pcmpt.2: |- ( ph -> A. n e. Prime A e. NN0 )
  assume pcmpt.3: |- ( ph -> N e. NN )
  assume pcmptdvds.3: |- ( ph -> M e. ( ZZ>= ` N ) )


  assert |- ( ph -> ( seq 1 ( x. , F ) ` N ) || ( seq 1 ( x. , F ) ` M ) )

  proof
    wph
    cN
    cmul
    cF
    c1
    cseq
    #
    cfv
    #
    cM
    @0
    cfv
    #
    cdvds
    wbr
    #
    @2
    @1
    cdiv
    co
    #
    cz
    wcel
    #
    wph
    @5
    cc0
    vp
    cv
    #
    @4
    cpc
    co
    #
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    wph
    @8
    vp
    cprime
    wph
    @6
    cprime
    wcel
    #
    wa
    #
    cc0
    @6
    cM
    cle
    wbr
    @6
    cN
    cle
    wbr
    wn
    wa
    #
    vn
    @6
    cA
    csb
    #
    cc0
    cif
    #
    @7
    cle
    @11
    cc0
    @13
    cle
    wbr
    #
    cc0
    cc0
    cle
    wbr
    #
    cc0
    @14
    cle
    wbr
    #
    @11
    @13
    wph
    vn
    vm
    cv
    #
    cA
    csb
    #
    cn0
    wcel
    #
    vm
    cprime
    wral
    #
    @10
    @13
    cn0
    wcel
    #
    wph
    cA
    cn0
    wcel
    #
    vn
    cprime
    wral
    @21
    pcmpt.2
    @23
    @20
    vn
    vm
    cprime
    @23
    vm
    nfv
    vn
    @19
    cn0
    vn
    @18
    cA
    nfcsb1v
    #
    nfel1
    vn
    vm
    weq
    #
    cA
    @19
    cn0
    vn
    @18
    cA
    csbeq1a
    #
    eleq1d
    cbvral
    sylib
    #
    @20
    @22
    vm
    @6
    cprime
    vm
    vp
    weq
    @19
    @13
    cn0
    vn
    @18
    @6
    cA
    csbeq1
    #
    eleq1d
    rspcv
    mpan9
    nn0ge0d
    0le0
    @12
    @15
    @16
    @17
    @13
    cc0
    @13
    @14
    cc0
    cle
    breq2
    cc0
    @14
    cc0
    cle
    breq2
    ifboth
    sylancl
    @11
    @19
    @13
    @6
    vm
    cF
    cM
    cN
    cF
    vn
    cn
    vn
    cv
    #
    cprime
    wcel
    #
    @29
    cA
    cexp
    co
    #
    c1
    cif
    #
    cmpt
    vm
    cn
    @18
    cprime
    wcel
    #
    @18
    @19
    cexp
    co
    #
    c1
    cif
    #
    cmpt
    pcmpt.1
    vn
    vm
    cn
    @32
    @35
    vm
    @32
    nfcv
    @33
    vn
    @34
    c1
    @33
    vn
    nfv
    vn
    @18
    @19
    cexp
    vn
    @18
    nfcv
    vn
    cexp
    nfcv
    @24
    nfov
    vn
    c1
    nfcv
    nfif
    @25
    @30
    @33
    @31
    @34
    c1
    @29
    @18
    cprime
    eleq1
    @25
    @29
    @18
    cA
    @19
    cexp
    @25
    id
    @26
    oveq12d
    ifbieq1d
    cbvmpt
    eqtri
    wph
    @21
    @10
    @27
    adantr
    wph
    cN
    cn
    wcel
    #
    @10
    pcmpt.3
    adantr
    wph
    @10
    simpr
    @28
    wph
    cM
    cN
    cuz
    cfv
    wcel
    #
    @10
    pcmptdvds.3
    adantr
    pcmpt2
    breqtrrd
    ralrimiva
    wph
    @4
    cq
    wcel
    #
    @5
    @9
    wb
    wph
    @2
    cz
    wcel
    #
    @1
    cn
    wcel
    @38
    wph
    @2
    wph
    cn
    cn
    cM
    @0
    wph
    cn
    cn
    cF
    wf
    cn
    cn
    @0
    wf
    wph
    cA
    vn
    cF
    pcmpt.1
    pcmpt.2
    pcmptcl
    simprd
    #
    wph
    @36
    @37
    cM
    cn
    wcel
    pcmpt.3
    pcmptdvds.3
    cM
    cN
    eluznn
    syl2anc
    ffvelrnd
    nnzd
    #
    wph
    cn
    cn
    cN
    @0
    @40
    pcmpt.3
    ffvelrnd
    #
    @2
    @1
    znq
    syl2anc
    @4
    vp
    pcz
    syl
    mpbird
    wph
    @1
    cz
    wcel
    @1
    cc0
    wne
    @39
    @3
    @5
    wb
    wph
    @1
    @42
    nnzd
    wph
    @1
    @42
    nnne0d
    @41
    @1
    @2
    dvdsval2
    syl3anc
    mpbird
end
