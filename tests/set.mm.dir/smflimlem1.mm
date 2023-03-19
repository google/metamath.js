include "cin.mm"
include "csalg.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cli.mm"
include "cdm.mm"
include "cuz.mm"
include "ciin.mm"
include "ciun.mm"
include "crab.mm"
include "wral.mm"
include "fvex.mm"
include "eqeltri.mm"
include "c0.mm"
include "wne.mm"
include "cz.mm"
include "uzssz.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "sseldi.mm"
include "uzid.mm"
include "syl.mm"
include "ne0i.mm"
include "dmex.mm"
include "rgenw.mm"
include "a1i.mm"
include "iinexg.mm"
include "syl2anc.mm"
include "rgen.mm"
include "iunexg.mm"
include "mp2an.mm"
include "rabex.mm"
include "cn.mm"
include "co.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "nnct.mm"
include "nnn0.mm"
include "wa.mm"
include "adantr.mm"
include "uzct.mm"
include "eqid.mm"
include "adantl.mm"
include "simpll.mm"
include "adantllr.mm"
include "adantlll.mm"
include "uztrn2.mm"
include "ssd.mm"
include "sselda.mm"
include "adantll.mm"
include "w3a.mm"
include "wceq.mm"
include "simp3.mm"
include "simp2.mm"
include "ovmpt4g.mm"
include "syl3anc.mm"
include "c1.mm"
include "cdiv.mm"
include "caddc.mm"
include "clt.mm"
include "simp1.mm"
include "rabexd.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "crn.mm"
include "ralrimivw.mm"
include "3ad2ant1.mm"
include "elrnmpt2id.mm"
include "wi.mm"
include "ovex.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "vtocl.mm"
include "sseldd.mm"
include "eqeltrd.mm"
include "saliincl.mm"
include "saliuncl.mm"
include "syl5eqel.mm"
include "incom.mm"
include "elrestd.mm"

theorem smflimlem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cS: class S
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cI: class I
  let cM: class M
  let cZ: class Z
  let vs: setvar s
  let vr: setvar r
  let vj: setvar j
  assume smflimlem1.1: |- Z = ( ZZ>= ` M )
  assume smflimlem1.2: |- ( ph -> S e. SAlg )
  assume smflimlem1.3: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( m e. Z |-> ( ( F ` m ) ` x ) ) e. dom ~~> }
  assume smflimlem1.4: |- P = ( m e. Z , k e. NN |-> { s e. S | { x e. dom ( F ` m ) | ( ( F ` m ) ` x ) < ( A + ( 1 / k ) ) } = ( s i^i dom ( F ` m ) ) } )
  assume smflimlem1.5: |- H = ( m e. Z , k e. NN |-> ( C ` ( m P k ) ) )
  assume smflimlem1.6: |- I = |^|_ k e. NN U_ n e. Z |^|_ m e. ( ZZ>= ` n ) ( m H k )
  assume smflimlem1.7: |- ( ( ph /\ r e. ran P ) -> ( C ` r ) e. r )

  disjoint C r
  disjoint F x
  disjoint P r
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint S s
  disjoint Z n
  disjoint Z k
  disjoint Z m
  disjoint Z x
  disjoint m x
  disjoint n x
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint k r
  disjoint m r
  disjoint ph r
  disjoint k x
  disjoint Z j
  disjoint j n
  assert |- ( ph -> ( D i^i I ) e. ( S |`t D ) )

  proof
    wph
    cD
    cI
    cin
    cD
    cS
    csalg
    cvv
    cI
    smflimlem1.2
    cD
    cvv
    wcel
    wph
    cD
    vm
    cZ
    vx
    cv
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    cli
    cdm
    wcel
    #
    vx
    vn
    cZ
    vm
    vn
    cv
    #
    cuz
    cfv
    #
    @1
    cdm
    #
    ciin
    #
    ciun
    #
    crab
    cvv
    smflimlem1.3
    @3
    vx
    @8
    cZ
    cvv
    wcel
    @7
    cvv
    wcel
    #
    vn
    cZ
    wral
    @8
    cvv
    wcel
    cZ
    cM
    cuz
    cfv
    #
    cvv
    smflimlem1.1
    cM
    cuz
    fvex
    eqeltri
    @9
    vn
    cZ
    @4
    cZ
    wcel
    #
    @5
    c0
    wne
    #
    @6
    cvv
    wcel
    #
    vm
    @5
    wral
    #
    @9
    @11
    @4
    @5
    wcel
    #
    @12
    @11
    @4
    cz
    wcel
    @15
    @11
    @10
    cz
    @4
    cM
    uzssz
    @11
    @4
    @10
    wcel
    cZ
    @10
    @4
    smflimlem1.1
    eleq2i
    biimpi
    sseldi
    @4
    uzid
    syl
    @5
    @4
    ne0i
    syl
    #
    @14
    @11
    @13
    vm
    @5
    @1
    @0
    cF
    fvex
    dmex
    rgenw
    a1i
    vm
    @5
    @6
    cvv
    iinexg
    syl2anc
    rgen
    vn
    cZ
    @7
    cvv
    cvv
    iunexg
    mp2an
    rabex
    eqeltri
    a1i
    wph
    cI
    vk
    cn
    vn
    cZ
    vm
    @5
    @0
    vk
    cv
    #
    cH
    co
    #
    ciin
    #
    ciun
    #
    ciin
    cS
    smflimlem1.6
    wph
    cS
    vk
    @20
    cn
    smflimlem1.2
    cn
    com
    cdom
    wbr
    wph
    nnct
    a1i
    cn
    c0
    wne
    wph
    nnn0
    a1i
    wph
    @17
    cn
    wcel
    #
    wa
    #
    cS
    vn
    @19
    cZ
    wph
    cS
    csalg
    wcel
    #
    @21
    smflimlem1.2
    adantr
    #
    cZ
    com
    cdom
    wbr
    @22
    cM
    cZ
    smflimlem1.1
    uzct
    a1i
    @22
    @11
    wa
    #
    cS
    vm
    @18
    @5
    @22
    @23
    @11
    @24
    adantr
    @5
    com
    cdom
    wbr
    @25
    @4
    @5
    @5
    eqid
    uzct
    a1i
    @11
    @12
    @22
    @16
    adantl
    @25
    @0
    @5
    wcel
    #
    wa
    wph
    @21
    @0
    cZ
    wcel
    #
    @18
    cS
    wcel
    wph
    @11
    @26
    wph
    @21
    wph
    @11
    @26
    simpll
    adantllr
    @21
    @11
    @26
    @21
    wph
    @21
    @11
    @26
    simpll
    adantlll
    @11
    @26
    @27
    @22
    @11
    @5
    cZ
    @0
    @11
    vj
    @5
    cZ
    cM
    vj
    cv
    @4
    cZ
    smflimlem1.1
    uztrn2
    ssd
    sselda
    adantll
    wph
    @21
    @27
    w3a
    #
    @18
    @0
    @17
    cP
    co
    #
    cC
    cfv
    #
    cS
    @28
    @27
    @21
    @30
    cvv
    wcel
    #
    @18
    @30
    wceq
    wph
    @21
    @27
    simp3
    #
    wph
    @21
    @27
    simp2
    #
    @31
    @28
    @29
    cC
    fvex
    a1i
    vm
    vk
    cZ
    cn
    @30
    cH
    cvv
    smflimlem1.5
    ovmpt4g
    syl3anc
    @28
    @29
    cS
    @30
    @28
    @29
    @2
    cA
    c1
    @17
    cdiv
    co
    caddc
    co
    clt
    wbr
    vx
    @6
    crab
    vs
    cv
    @6
    cin
    wceq
    #
    vs
    cS
    crab
    #
    cS
    @28
    @27
    @21
    @35
    cvv
    wcel
    #
    @29
    @35
    wceq
    @32
    @33
    @28
    wph
    @36
    wph
    @21
    @27
    simp1
    #
    wph
    @34
    vs
    cS
    @35
    csalg
    @35
    eqid
    smflimlem1.2
    rabexd
    #
    syl
    vm
    vk
    cZ
    cn
    @35
    cP
    cvv
    smflimlem1.4
    ovmpt4g
    syl3anc
    @34
    vs
    cS
    ssrab2
    syl6eqss
    @28
    wph
    @29
    cP
    crn
    #
    wcel
    #
    @30
    @29
    wcel
    #
    @37
    @28
    @27
    @21
    @36
    vk
    cn
    wral
    #
    vm
    cZ
    wral
    #
    @40
    @32
    @33
    wph
    @21
    @43
    @27
    wph
    @42
    vm
    cZ
    wph
    @36
    vk
    cn
    @38
    ralrimivw
    ralrimivw
    3ad2ant1
    vm
    vk
    cZ
    cn
    @35
    cP
    cvv
    smflimlem1.4
    elrnmpt2id
    syl3anc
    wph
    vr
    cv
    #
    @39
    wcel
    #
    wa
    #
    @44
    cC
    cfv
    #
    @44
    wcel
    #
    wi
    wph
    @40
    wa
    #
    @41
    wi
    vr
    @29
    @0
    @17
    cP
    ovex
    @44
    @29
    wceq
    #
    @46
    @49
    @48
    @41
    @50
    @45
    @40
    wph
    @44
    @29
    @39
    eleq1
    anbi2d
    @50
    @47
    @30
    @44
    @29
    @44
    @29
    cC
    fveq2
    @50
    id
    eleq12d
    imbi12d
    smflimlem1.7
    vtocl
    syl2anc
    sseldd
    eqeltrd
    syl3anc
    saliincl
    saliuncl
    saliincl
    syl5eqel
    cD
    cI
    incom
    elrestd
end
