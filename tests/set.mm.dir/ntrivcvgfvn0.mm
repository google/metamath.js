include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "cseq.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cli.mm"
include "wfun.mm"
include "wbr.mm"
include "cdm.mm"
include "cc.mm"
include "wf.mm"
include "fclim.mm"
include "ffun.mm"
include "ax-mp.mm"
include "funbrfv.mm"
include "mpsyl.mm"
include "adantr.mm"
include "cvv.mm"
include "cuz.mm"
include "eqid.mm"
include "cz.mm"
include "wcel.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "seqex.mm"
include "a1i.mm"
include "0cnd.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "weq.mm"
include "simpr.mm"
include "w3a.mm"
include "syl6eleq.mm"
include "uztrn.mm"
include "sylan2.mm"
include "3adant3.mm"
include "seqp1.mm"
include "syl.mm"
include "oveq1.mm"
include "3ad2ant3.mm"
include "peano2uz.mm"
include "uztrn2.mm"
include "syl2an.mm"
include "wral.mm"
include "ralrimiva.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "mpan9.mm"
include "syldan.mm"
include "ancoms.mm"
include "mul02d.mm"
include "3eqtrd.mm"
include "3exp.mm"
include "adantrd.mm"
include "a2d.mm"
include "uzind4.mm"
include "impcom.mm"
include "climconst.mm"
include "eqtr3d.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"

theorem ntrivcvgfvn0
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vm: setvar m
  let vn: setvar n
  assume ntrivcvgfvn0.1: |- Z = ( ZZ>= ` M )
  assume ntrivcvgfvn0.2: |- ( ph -> N e. Z )
  assume ntrivcvgfvn0.3: |- ( ph -> seq M ( x. , F ) ~~> X )
  assume ntrivcvgfvn0.4: |- ( ph -> X =/= 0 )
  assume ntrivcvgfvn0.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )

  disjoint F k
  disjoint k ph
  disjoint M k
  disjoint N k
  disjoint Z k
  disjoint F m
  disjoint F n
  disjoint k m
  disjoint k n
  disjoint M m
  disjoint m n
  disjoint M n
  disjoint m ph
  disjoint N m
  disjoint N n
  disjoint n ph
  assert |- ( ph -> ( seq M ( x. , F ) ` N ) =/= 0 )

  proof
    wph
    cX
    cc0
    wne
    cN
    cmul
    cF
    cM
    cseq
    #
    cfv
    #
    cc0
    wne
    ntrivcvgfvn0.4
    wph
    @1
    cc0
    cX
    cc0
    wph
    @1
    cc0
    wceq
    #
    cX
    cc0
    wceq
    wph
    @2
    wa
    #
    @0
    cli
    cfv
    #
    cX
    cc0
    wph
    @4
    cX
    wceq
    #
    @2
    cli
    wfun
    #
    wph
    @0
    cX
    cli
    wbr
    @5
    cli
    cdm
    #
    cc
    cli
    wf
    @6
    fclim
    @7
    cc
    cli
    ffun
    ax-mp
    #
    ntrivcvgfvn0.3
    @0
    cX
    cli
    funbrfv
    mpsyl
    adantr
    @6
    @3
    @0
    cc0
    cli
    wbr
    @4
    cc0
    wceq
    @8
    @3
    cc0
    vk
    @0
    cN
    cvv
    cN
    cuz
    cfv
    #
    @9
    eqid
    wph
    cN
    cz
    wcel
    #
    @2
    wph
    cZ
    cz
    cN
    cZ
    cM
    cuz
    cfv
    #
    cz
    ntrivcvgfvn0.1
    cM
    uzssz
    eqsstri
    ntrivcvgfvn0.2
    sseldi
    adantr
    @0
    cvv
    wcel
    @3
    cmul
    cF
    cM
    seqex
    a1i
    @3
    0cnd
    vk
    cv
    #
    @9
    wcel
    @3
    @12
    @0
    cfv
    #
    cc0
    wceq
    #
    @3
    vm
    cv
    #
    @0
    cfv
    #
    cc0
    wceq
    #
    wi
    @3
    @2
    wi
    #
    @3
    vn
    cv
    #
    @0
    cfv
    #
    cc0
    wceq
    #
    wi
    @3
    @19
    c1
    caddc
    co
    #
    @0
    cfv
    #
    cc0
    wceq
    #
    wi
    @3
    @14
    wi
    vm
    vn
    cN
    @12
    @15
    cN
    wceq
    #
    @17
    @2
    @3
    @25
    @16
    @1
    cc0
    @15
    cN
    @0
    fveq2
    eqeq1d
    imbi2d
    vm
    vn
    weq
    #
    @17
    @21
    @3
    @26
    @16
    @20
    cc0
    @15
    @19
    @0
    fveq2
    eqeq1d
    imbi2d
    @15
    @22
    wceq
    #
    @17
    @24
    @3
    @27
    @16
    @23
    cc0
    @15
    @22
    @0
    fveq2
    eqeq1d
    imbi2d
    vm
    vk
    weq
    #
    @17
    @14
    @3
    @28
    @16
    @13
    cc0
    @15
    @12
    @0
    fveq2
    eqeq1d
    imbi2d
    @18
    @10
    wph
    @2
    simpr
    a1i
    @19
    @9
    wcel
    #
    @3
    @21
    @24
    @29
    wph
    @21
    @24
    wi
    @2
    @29
    wph
    @21
    @24
    @29
    wph
    @21
    w3a
    #
    @23
    @20
    @22
    cF
    cfv
    #
    cmul
    co
    #
    cc0
    @31
    cmul
    co
    #
    cc0
    @30
    @19
    @11
    wcel
    #
    @23
    @32
    wceq
    @29
    wph
    @34
    @21
    wph
    @29
    cN
    @11
    wcel
    @34
    wph
    cN
    cZ
    @11
    ntrivcvgfvn0.2
    ntrivcvgfvn0.1
    syl6eleq
    cN
    @19
    cM
    uztrn
    sylan2
    3adant3
    cmul
    cF
    cM
    @19
    seqp1
    syl
    @21
    @29
    @32
    @33
    wceq
    wph
    @20
    cc0
    @31
    cmul
    oveq1
    3ad2ant3
    @29
    wph
    @33
    cc0
    wceq
    @21
    @29
    wph
    wa
    @31
    wph
    @29
    @31
    cc
    wcel
    #
    wph
    @29
    @22
    cZ
    wcel
    #
    @35
    wph
    cN
    cZ
    wcel
    @22
    @9
    wcel
    @36
    @29
    ntrivcvgfvn0.2
    cN
    @19
    peano2uz
    cM
    @22
    cN
    cZ
    ntrivcvgfvn0.1
    uztrn2
    syl2an
    wph
    @12
    cF
    cfv
    #
    cc
    wcel
    #
    vk
    cZ
    wral
    @36
    @35
    wph
    @38
    vk
    cZ
    ntrivcvgfvn0.5
    ralrimiva
    @38
    @35
    vk
    @22
    cZ
    @12
    @22
    wceq
    @37
    @31
    cc
    @12
    @22
    cF
    fveq2
    eleq1d
    rspcv
    mpan9
    syldan
    ancoms
    mul02d
    3adant3
    3eqtrd
    3exp
    adantrd
    a2d
    uzind4
    impcom
    climconst
    @0
    cc0
    cli
    funbrfv
    mpsyl
    eqtr3d
    ex
    necon3d
    mpd
end
