include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "csmu.mm"
include "wb.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "bibi2d.mm"
include "imbi2d.mm"
include "cz.mm"
include "smuval.mm"
include "a1i.mm"
include "wa.mm"
include "cmin.mm"
include "cn0.mm"
include "crab.mm"
include "csad.mm"
include "wss.mm"
include "adantr.mm"
include "peano2nn0.mm"
include "syl.mm"
include "eluznn0.mm"
include "sylan.mm"
include "smupp1.mm"
include "cc0.mm"
include "cfzo.mm"
include "cin.mm"
include "cpw.mm"
include "smupf.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "ssrab2.mm"
include "sadeq.mm"
include "c0.mm"
include "inrab2.mm"
include "wn.mm"
include "wral.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "inss1.mm"
include "simpr.mm"
include "sseldi.mm"
include "nn0red.mm"
include "1red.mm"
include "readdcld.mm"
include "inss2.mm"
include "elfzolt2.mm"
include "eluzle.mm"
include "ad2antlr.mm"
include "ltletrd.mm"
include "ltnled.mm"
include "mpbid.mm"
include "sseld.mm"
include "nn0ge0.mm"
include "syl6.mm"
include "subge0d.mm"
include "sylibd.mm"
include "adantld.mm"
include "mtod.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "syl5ss.mm"
include "sadid1.mm"
include "eqtrd.mm"
include "ineq1d.mm"
include "inass.mm"
include "inidm.mm"
include "ineq2i.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "elin.mm"
include "3bitr3g.mm"
include "cfz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "nn0zd.mm"
include "fzval3.mm"
include "eleqtrd.mm"
include "biantrud.mm"
include "3bitr4d.mm"
include "bitrd.mm"
include "biimprd.mm"
include "expcom.mm"
include "a2d.mm"
include "uzind4.mm"
include "mpcom.mm"

theorem smuval2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let vm: setvar m
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume smuval.a: |- ( ph -> A C_ NN0 )
  assume smuval.b: |- ( ph -> B C_ NN0 )
  assume smuval.p: |- P = seq 0 ( ( p e. ~P NN0 , m e. NN0 |-> ( p sadd { n e. NN0 | ( m e. A /\ ( n - m ) e. B ) } ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )
  assume smuval.n: |- ( ph -> N e. NN0 )
  assume smuval2.m: |- ( ph -> M e. ( ZZ>= ` ( N + 1 ) ) )

  disjoint m n
  disjoint m p
  disjoint A m
  disjoint n p
  disjoint A n
  disjoint A p
  disjoint N n
  disjoint n ph
  disjoint B m
  disjoint B n
  disjoint B p
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint p x
  disjoint p y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint M k
  disjoint M x
  disjoint P k
  disjoint P x
  disjoint P y
  assert |- ( ph -> ( N e. ( A smul B ) <-> N e. ( P ` M ) ) )

  proof
    cM
    cN
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    wph
    cN
    cA
    cB
    csmu
    co
    wcel
    #
    cN
    cM
    cP
    cfv
    #
    wcel
    #
    wb
    #
    smuval2.m
    wph
    @2
    cN
    vx
    cv
    #
    cP
    cfv
    #
    wcel
    #
    wb
    #
    wi
    wph
    @2
    cN
    @0
    cP
    cfv
    #
    wcel
    #
    wb
    #
    wi
    #
    wph
    @2
    cN
    vk
    cv
    #
    cP
    cfv
    #
    wcel
    #
    wb
    #
    wi
    wph
    @2
    cN
    @14
    c1
    caddc
    co
    #
    cP
    cfv
    #
    wcel
    #
    wb
    #
    wi
    wph
    @5
    wi
    vx
    vk
    @0
    cM
    @6
    @0
    wceq
    #
    @9
    @12
    wph
    @22
    @8
    @11
    @2
    @22
    @7
    @10
    cN
    @6
    @0
    cP
    fveq2
    eleq2d
    bibi2d
    imbi2d
    @6
    @14
    wceq
    #
    @9
    @17
    wph
    @23
    @8
    @16
    @2
    @23
    @7
    @15
    cN
    @6
    @14
    cP
    fveq2
    eleq2d
    bibi2d
    imbi2d
    @6
    @18
    wceq
    #
    @9
    @21
    wph
    @24
    @8
    @20
    @2
    @24
    @7
    @19
    cN
    @6
    @18
    cP
    fveq2
    eleq2d
    bibi2d
    imbi2d
    @6
    cM
    wceq
    #
    @9
    @5
    wph
    @25
    @8
    @4
    @2
    @25
    @7
    @3
    cN
    @6
    cM
    cP
    fveq2
    eleq2d
    bibi2d
    imbi2d
    @13
    @0
    cz
    wcel
    wph
    cA
    cB
    cP
    vm
    vn
    cN
    vp
    smuval.a
    smuval.b
    smuval.p
    smuval.n
    smuval
    a1i
    @14
    @1
    wcel
    #
    wph
    @17
    @21
    wph
    @26
    @17
    @21
    wi
    wph
    @26
    wa
    #
    @21
    @17
    @27
    @20
    @16
    @2
    @27
    @20
    cN
    @15
    @14
    cA
    wcel
    #
    vn
    cv
    #
    @14
    cmin
    co
    #
    cB
    wcel
    #
    wa
    #
    vn
    cn0
    crab
    #
    csad
    co
    #
    wcel
    #
    @16
    @27
    @19
    @34
    cN
    @27
    cA
    cB
    cP
    vm
    vn
    @14
    vp
    wph
    cA
    cn0
    wss
    @26
    smuval.a
    adantr
    #
    wph
    cB
    cn0
    wss
    #
    @26
    smuval.b
    adantr
    #
    smuval.p
    wph
    @0
    cn0
    wcel
    #
    @26
    @14
    cn0
    wcel
    #
    wph
    cN
    cn0
    wcel
    #
    @39
    smuval.n
    cN
    peano2nn0
    syl
    #
    @14
    @0
    eluznn0
    sylan
    #
    smupp1
    eleq2d
    @27
    @35
    cN
    cc0
    @0
    cfzo
    co
    #
    wcel
    #
    wa
    #
    @16
    @45
    wa
    #
    @35
    @16
    @27
    cN
    @34
    @44
    cin
    #
    wcel
    cN
    @15
    @44
    cin
    #
    wcel
    @46
    @47
    @27
    @48
    @49
    cN
    @27
    @48
    @49
    @33
    @44
    cin
    #
    csad
    co
    #
    @44
    cin
    #
    @49
    @27
    @15
    @33
    @0
    @27
    @15
    cn0
    @27
    cn0
    cn0
    cpw
    @14
    cP
    @27
    cA
    cB
    cP
    vm
    vn
    vp
    @36
    @38
    smuval.p
    smupf
    @43
    ffvelrnd
    elpwid
    #
    @33
    cn0
    wss
    @27
    @32
    vn
    cn0
    ssrab2
    a1i
    wph
    @39
    @26
    @42
    adantr
    sadeq
    @27
    @52
    @49
    @44
    cin
    #
    @49
    @27
    @51
    @49
    @44
    @27
    @51
    @49
    c0
    csad
    co
    #
    @49
    @27
    @50
    c0
    @49
    csad
    @27
    @50
    @32
    vn
    cn0
    @44
    cin
    #
    crab
    #
    c0
    @32
    vn
    cn0
    @44
    inrab2
    @27
    @32
    wn
    #
    vn
    @56
    wral
    @57
    c0
    wceq
    @27
    @58
    vn
    @56
    @27
    @29
    @56
    wcel
    #
    wa
    #
    @32
    @14
    @29
    cle
    wbr
    #
    @60
    @29
    @14
    clt
    wbr
    @61
    wn
    @60
    @29
    @0
    @14
    @60
    @29
    @60
    @56
    cn0
    @29
    cn0
    @44
    inss1
    @27
    @59
    simpr
    #
    sseldi
    nn0red
    #
    @60
    cN
    c1
    @60
    cN
    @27
    @41
    @59
    wph
    @41
    @26
    smuval.n
    adantr
    #
    adantr
    nn0red
    @60
    1red
    readdcld
    @60
    @14
    @27
    @40
    @59
    @43
    adantr
    nn0red
    #
    @60
    @29
    @44
    wcel
    @29
    @0
    clt
    wbr
    @60
    @56
    @44
    @29
    cn0
    @44
    inss2
    @62
    sseldi
    @29
    cc0
    @0
    elfzolt2
    syl
    @26
    @0
    @14
    cle
    wbr
    wph
    @59
    @0
    @14
    eluzle
    ad2antlr
    ltletrd
    @60
    @29
    @14
    @63
    @65
    ltnled
    mpbid
    @60
    @31
    @61
    @28
    @60
    @31
    cc0
    @30
    cle
    wbr
    #
    @61
    @60
    @31
    @30
    cn0
    wcel
    @66
    @60
    cB
    cn0
    @30
    @27
    @37
    @59
    @38
    adantr
    sseld
    @30
    nn0ge0
    syl6
    @60
    @29
    @14
    @63
    @65
    subge0d
    sylibd
    adantld
    mtod
    ralrimiva
    @32
    vn
    @56
    rabeq0
    sylibr
    syl5eq
    oveq2d
    @27
    @49
    cn0
    wss
    @55
    @49
    wceq
    @27
    @49
    @15
    cn0
    @15
    @44
    inss1
    @53
    syl5ss
    @49
    sadid1
    syl
    eqtrd
    ineq1d
    @54
    @15
    @44
    @44
    cin
    #
    cin
    @49
    @15
    @44
    @44
    inass
    @67
    @44
    @15
    @44
    inidm
    ineq2i
    eqtri
    syl6eq
    eqtrd
    eleq2d
    cN
    @34
    @44
    elin
    cN
    @15
    @44
    elin
    3bitr3g
    @27
    @45
    @35
    @27
    cN
    cc0
    cN
    cfz
    co
    #
    @44
    @27
    cN
    cc0
    cuz
    cfv
    #
    wcel
    cN
    @68
    wcel
    @27
    cN
    cn0
    @69
    @64
    nn0uz
    syl6eleq
    cc0
    cN
    eluzfz2
    syl
    @27
    cN
    cz
    wcel
    @68
    @44
    wceq
    @27
    cN
    @64
    nn0zd
    cc0
    cN
    fzval3
    syl
    eleqtrd
    #
    biantrud
    @27
    @45
    @16
    @70
    biantrud
    3bitr4d
    bitrd
    bibi2d
    biimprd
    expcom
    a2d
    uzind4
    mpcom
end
