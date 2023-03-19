include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cseq.mm"
include "cfv.mm"
include "cdiv.mm"
include "cli.mm"
include "cvv.mm"
include "cuz.mm"
include "eqid.mm"
include "wcel.mm"
include "cz.mm"
include "eluzelz.mm"
include "eleq2s.mm"
include "syl.mm"
include "peano2zd.mm"
include "cc.mm"
include "eluzel2.mm"
include "prodf.mm"
include "ffvelrnd.mm"
include "reccld.mm"
include "seqex.mm"
include "a1i.mm"
include "cv.mm"
include "syl6eleq.mm"
include "peano2uz.mm"
include "syl6eleqr.mm"
include "uztrn2.mm"
include "sylan.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "wa.mm"
include "wceq.mm"
include "mulcl.mm"
include "adantl.mm"
include "w3a.mm"
include "mulass.mm"
include "simpr.mm"
include "adantr.mm"
include "cfz.mm"
include "elfzuz.mm"
include "sylan2.mm"
include "adantlr.mm"
include "seqsplit.mm"
include "eqcomd.mm"
include "cc0.mm"
include "wne.mm"
include "divmuld.mm"
include "mpbird.mm"
include "divrec2d.mm"
include "eqtr3d.mm"
include "climmulc2.mm"
include "wbr.mm"
include "climcl.mm"
include "breqtrrd.mm"

theorem clim2div
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  assume clim2div.1: |- Z = ( ZZ>= ` M )
  assume clim2div.2: |- ( ph -> N e. Z )
  assume clim2div.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume clim2div.4: |- ( ph -> seq M ( x. , F ) ~~> A )
  assume clim2div.5: |- ( ph -> ( seq M ( x. , F ) ` N ) =/= 0 )

  disjoint F k
  disjoint k ph
  disjoint M k
  disjoint N k
  disjoint Z k
  disjoint A j
  disjoint F j
  disjoint F x
  disjoint F y
  disjoint j k
  disjoint j ph
  disjoint j x
  disjoint j y
  disjoint k x
  disjoint k y
  disjoint M j
  disjoint M x
  disjoint M y
  disjoint N j
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint x y
  assert |- ( ph -> seq ( N + 1 ) ( x. , F ) ~~> ( A / ( seq M ( x. , F ) ` N ) ) )

  proof
    wph
    cmul
    cF
    cN
    c1
    caddc
    co
    #
    cseq
    #
    c1
    cN
    cmul
    cF
    cM
    cseq
    #
    cfv
    #
    cdiv
    co
    #
    cA
    cmul
    co
    cA
    @3
    cdiv
    co
    cli
    wph
    cA
    @4
    vj
    @2
    @1
    @0
    cvv
    @0
    cuz
    cfv
    #
    @5
    eqid
    #
    wph
    cN
    wph
    cN
    cZ
    wcel
    #
    cN
    cz
    wcel
    #
    clim2div.2
    @8
    cN
    cM
    cuz
    cfv
    #
    cZ
    cM
    cN
    eluzelz
    clim2div.1
    eleq2s
    syl
    peano2zd
    #
    clim2div.4
    wph
    @3
    wph
    cZ
    cc
    cN
    @2
    wph
    vk
    cF
    cM
    cZ
    clim2div.1
    wph
    @7
    cM
    cz
    wcel
    #
    clim2div.2
    @11
    cN
    @9
    cZ
    cM
    cN
    eluzel2
    clim2div.1
    eleq2s
    syl
    clim2div.3
    prodf
    #
    clim2div.2
    ffvelrnd
    #
    clim2div.5
    reccld
    @1
    cvv
    wcel
    wph
    cmul
    cF
    @0
    seqex
    a1i
    wph
    vj
    cv
    #
    @5
    wcel
    #
    @14
    cZ
    wcel
    #
    @14
    @2
    cfv
    #
    cc
    wcel
    wph
    @0
    cZ
    wcel
    #
    @15
    @16
    wph
    @0
    @9
    cZ
    wph
    cN
    @9
    wcel
    #
    @0
    @9
    wcel
    wph
    cN
    cZ
    @9
    clim2div.2
    clim2div.1
    syl6eleq
    #
    cM
    cN
    peano2uz
    syl
    clim2div.1
    syl6eleqr
    #
    cM
    @14
    @0
    cZ
    clim2div.1
    uztrn2
    sylan
    wph
    cZ
    cc
    @14
    @2
    @12
    ffvelrnda
    syldan
    #
    wph
    @15
    wa
    #
    @17
    @3
    cdiv
    co
    #
    @14
    @1
    cfv
    #
    @4
    @17
    cmul
    co
    @23
    @24
    @25
    wceq
    @3
    @25
    cmul
    co
    #
    @17
    wceq
    @23
    @17
    @26
    @23
    vk
    vx
    vy
    cmul
    cc
    cF
    cM
    cN
    @14
    vk
    cv
    #
    cc
    wcel
    #
    vx
    cv
    #
    cc
    wcel
    #
    wa
    @27
    @29
    cmul
    co
    #
    cc
    wcel
    @23
    @27
    @29
    mulcl
    adantl
    @28
    @30
    vy
    cv
    #
    cc
    wcel
    w3a
    @31
    @32
    cmul
    co
    @27
    @29
    @32
    cmul
    co
    cmul
    co
    wceq
    @23
    @27
    @29
    @32
    mulass
    adantl
    wph
    @15
    simpr
    wph
    @19
    @15
    @20
    adantr
    wph
    @27
    cM
    @14
    cfz
    co
    wcel
    #
    @27
    cF
    cfv
    cc
    wcel
    #
    @15
    @33
    wph
    @27
    cZ
    wcel
    #
    @34
    @33
    @27
    @9
    cZ
    @27
    cM
    @14
    elfzuz
    clim2div.1
    syl6eleqr
    clim2div.3
    sylan2
    adantlr
    seqsplit
    eqcomd
    @23
    @17
    @3
    @25
    @22
    wph
    @3
    cc
    wcel
    @15
    @13
    adantr
    #
    wph
    @5
    cc
    @14
    @1
    wph
    vk
    cF
    @0
    @5
    @6
    @10
    wph
    @27
    @5
    wcel
    #
    @35
    @34
    wph
    @18
    @37
    @35
    @21
    cM
    @27
    @0
    cZ
    clim2div.1
    uztrn2
    sylan
    clim2div.3
    syldan
    prodf
    ffvelrnda
    wph
    @3
    cc0
    wne
    @15
    clim2div.5
    adantr
    #
    divmuld
    mpbird
    @23
    @17
    @3
    @22
    @36
    @38
    divrec2d
    eqtr3d
    climmulc2
    wph
    cA
    @3
    wph
    @2
    cA
    cli
    wbr
    cA
    cc
    wcel
    clim2div.4
    cA
    @2
    climcl
    syl
    @13
    clim2div.5
    divrec2d
    breqtrrd
end
