include "cfv.mm"
include "csmu.mm"
include "co.mm"
include "cv.mm"
include "cn0.mm"
include "wcel.mm"
include "cpw.mm"
include "smupf.mm"
include "cuz.mm"
include "eluznn0.mm"
include "syl2anc.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "sseld.mm"
include "c1.mm"
include "caddc.mm"
include "crab.mm"
include "smufval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "wb.mm"
include "wa.mm"
include "wss.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "adantr.mm"
include "uztrn.mm"
include "sylan.mm"
include "smuval2.mm"
include "bicomd.mm"
include "wceq.mm"
include "simpll.mm"
include "wi.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "cz.mm"
include "eqidd.mm"
include "a1i.mm"
include "cmin.mm"
include "csad.mm"
include "c0.mm"
include "smupp1.mm"
include "wn.mm"
include "wral.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "eluzle.mm"
include "adantl.mm"
include "cr.mm"
include "nn0red.mm"
include "lenltd.mm"
include "mpbid.mm"
include "cc0.mm"
include "cfzo.mm"
include "elfzolt2.mm"
include "syl6.mm"
include "adantrd.mm"
include "mtod.mm"
include "ralrimivw.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "oveq2d.mm"
include "wf.mm"
include "sadid1.mm"
include "syl.mm"
include "3eqtrd.mm"
include "biimprd.mm"
include "expcom.mm"
include "a2d.mm"
include "uzind4.mm"
include "sylc.mm"
include "simpr.mm"
include "eqtr4d.mm"
include "eleq2d.mm"
include "smuval.mm"
include "bitr4d.mm"
include "wo.mm"
include "nn0zd.mm"
include "peano2zd.mm"
include "uztric.mm"
include "mpjaodan.mm"
include "ex.mm"
include "pm5.21ndd.mm"
include "eqrdv.mm"

theorem smupvallem
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
  assume smupvallem.a: |- ( ph -> A C_ ( 0 ..^ N ) )
  assume smupvallem.m: |- ( ph -> M e. ( ZZ>= ` N ) )

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
  assert |- ( ph -> ( P ` M ) = ( A smul B ) )

  proof
    wph
    vk
    cM
    cP
    cfv
    #
    cA
    cB
    csmu
    co
    #
    wph
    vk
    cv
    #
    cn0
    wcel
    #
    @2
    @0
    wcel
    #
    @2
    @1
    wcel
    #
    wph
    @0
    cn0
    @2
    wph
    @0
    cn0
    wph
    cn0
    cn0
    cpw
    #
    cM
    cP
    wph
    cA
    cB
    cP
    vm
    vn
    vp
    smuval.a
    smuval.b
    smuval.p
    smupf
    #
    wph
    cN
    cn0
    wcel
    #
    cM
    cN
    cuz
    cfv
    #
    wcel
    #
    cM
    cn0
    wcel
    smuval.n
    smupvallem.m
    cM
    cN
    eluznn0
    syl2anc
    ffvelrnd
    elpwid
    sseld
    wph
    @1
    cn0
    @2
    wph
    @1
    @2
    @2
    c1
    caddc
    co
    #
    cP
    cfv
    #
    wcel
    #
    vk
    cn0
    crab
    cn0
    wph
    cA
    cB
    cP
    vk
    vm
    vn
    vp
    smuval.a
    smuval.b
    smuval.p
    smufval
    @13
    vk
    cn0
    ssrab2
    syl6eqss
    sseld
    wph
    @3
    @4
    @5
    wb
    #
    wph
    @3
    wa
    #
    cN
    @11
    cuz
    cfv
    #
    wcel
    #
    @14
    @11
    @9
    wcel
    #
    @15
    @17
    wa
    #
    @5
    @4
    @19
    cA
    cB
    cP
    vm
    vn
    cM
    @2
    vp
    wph
    cA
    cn0
    wss
    #
    @3
    @17
    smuval.a
    ad2antrr
    wph
    cB
    cn0
    wss
    #
    @3
    @17
    smuval.b
    ad2antrr
    smuval.p
    wph
    @3
    @17
    simplr
    @15
    @10
    @17
    cM
    @16
    wcel
    wph
    @10
    @3
    smupvallem.m
    adantr
    cN
    cM
    @11
    uztrn
    sylan
    smuval2
    bicomd
    @15
    @18
    wa
    #
    @4
    @13
    @5
    @22
    @0
    @12
    @2
    @22
    @0
    cN
    cP
    cfv
    #
    @12
    @22
    @10
    wph
    @0
    @23
    wceq
    #
    wph
    @10
    @3
    @18
    smupvallem.m
    ad2antrr
    wph
    @3
    @18
    simpll
    #
    wph
    vx
    cv
    #
    cP
    cfv
    #
    @23
    wceq
    #
    wi
    #
    wph
    @23
    @23
    wceq
    #
    wi
    #
    wph
    @2
    cP
    cfv
    #
    @23
    wceq
    #
    wi
    #
    wph
    @12
    @23
    wceq
    #
    wi
    #
    wph
    @24
    wi
    vx
    vk
    cN
    cM
    @26
    cN
    wceq
    #
    @28
    @30
    wph
    @37
    @27
    @23
    @23
    @26
    cN
    cP
    fveq2
    eqeq1d
    imbi2d
    #
    @26
    @2
    wceq
    #
    @28
    @33
    wph
    @39
    @27
    @32
    @23
    @26
    @2
    cP
    fveq2
    eqeq1d
    imbi2d
    #
    @26
    @11
    wceq
    #
    @28
    @35
    wph
    @41
    @27
    @12
    @23
    @26
    @11
    cP
    fveq2
    eqeq1d
    imbi2d
    #
    @26
    cM
    wceq
    #
    @28
    @24
    wph
    @43
    @27
    @0
    @23
    @26
    cM
    cP
    fveq2
    eqeq1d
    imbi2d
    @31
    cN
    cz
    wcel
    #
    wph
    @23
    eqidd
    a1i
    #
    @2
    @9
    wcel
    #
    wph
    @33
    @35
    wph
    @46
    @33
    @35
    wi
    wph
    @46
    wa
    #
    @35
    @33
    @47
    @12
    @32
    @23
    @47
    @12
    @32
    @2
    cA
    wcel
    #
    vn
    cv
    @2
    cmin
    co
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
    @32
    c0
    csad
    co
    #
    @32
    @47
    cA
    cB
    cP
    vm
    vn
    @2
    vp
    wph
    @20
    @46
    smuval.a
    adantr
    wph
    @21
    @46
    smuval.b
    adantr
    smuval.p
    wph
    @8
    @46
    @3
    smuval.n
    @2
    cN
    eluznn0
    sylan
    #
    smupp1
    @47
    @51
    c0
    @32
    csad
    @47
    @50
    wn
    #
    vn
    cn0
    wral
    @51
    c0
    wceq
    @47
    @54
    vn
    cn0
    @47
    @50
    @2
    cN
    clt
    wbr
    #
    @47
    cN
    @2
    cle
    wbr
    #
    @55
    wn
    @46
    @56
    wph
    cN
    @2
    eluzle
    adantl
    @47
    cN
    @2
    wph
    cN
    cr
    wcel
    @46
    wph
    cN
    smuval.n
    nn0red
    adantr
    @47
    @2
    @53
    nn0red
    lenltd
    mpbid
    @47
    @48
    @55
    @49
    @47
    @48
    @2
    cc0
    cN
    cfzo
    co
    #
    wcel
    @55
    @47
    cA
    @57
    @2
    wph
    cA
    @57
    wss
    @46
    smupvallem.a
    adantr
    sseld
    @2
    cc0
    cN
    elfzolt2
    syl6
    adantrd
    mtod
    ralrimivw
    @50
    vn
    cn0
    rabeq0
    sylibr
    oveq2d
    @47
    @32
    cn0
    wss
    @52
    @32
    wceq
    @47
    @32
    cn0
    @47
    cn0
    @6
    @2
    cP
    wph
    cn0
    @6
    cP
    wf
    @46
    @7
    adantr
    @53
    ffvelrnd
    elpwid
    @32
    sadid1
    syl
    3eqtrd
    eqeq1d
    biimprd
    expcom
    a2d
    #
    uzind4
    sylc
    @22
    @18
    wph
    @35
    @15
    @18
    simpr
    @25
    @29
    @31
    @34
    @36
    @36
    vx
    vk
    cN
    @11
    @38
    @40
    @42
    @42
    @45
    @58
    uzind4
    sylc
    eqtr4d
    eleq2d
    @22
    cA
    cB
    cP
    vm
    vn
    @2
    vp
    wph
    @20
    @3
    @18
    smuval.a
    ad2antrr
    wph
    @21
    @3
    @18
    smuval.b
    ad2antrr
    smuval.p
    wph
    @3
    @18
    simplr
    smuval
    bitr4d
    @15
    @11
    cz
    wcel
    @44
    @17
    @18
    wo
    @15
    @2
    @15
    @2
    wph
    @3
    simpr
    nn0zd
    peano2zd
    wph
    @44
    @3
    wph
    cN
    smuval.n
    nn0zd
    adantr
    @11
    cN
    uztric
    syl2anc
    mpjaodan
    ex
    pm5.21ndd
    eqrdv
end
