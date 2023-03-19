include "csmu.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "cn0.mm"
include "wn.mm"
include "wss.mm"
include "smucl.mm"
include "syl2anc.mm"
include "sseld.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "cpw.mm"
include "cmin.mm"
include "crab.mm"
include "csad.mm"
include "cmpt2.mm"
include "cc0.mm"
include "wceq.mm"
include "c0.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cfv.mm"
include "noel.mm"
include "wi.mm"
include "peano2nn0.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "eqid.mm"
include "smup0.mm"
include "oveq1.mm"
include "adantr.mm"
include "simpr.mm"
include "smupp1.mm"
include "wral.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "oveq2d.mm"
include "0ss.mm"
include "sadid1.mm"
include "mp1i.mm"
include "eqtr2d.mm"
include "eqeq12d.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "syl.mm"
include "impcom.mm"
include "eleq2d.mm"
include "mtbiri.mm"
include "smuval.mm"
include "mtbird.mm"
include "ex.mm"
include "syld.mm"
include "pm2.01d.mm"
include "eq0rdv.mm"

theorem smu01lem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let vm: setvar m
  let vp: setvar p
  let vx: setvar x
  assume smu01lem.1: |- ( ph -> A C_ NN0 )
  assume smu01lem.2: |- ( ph -> B C_ NN0 )
  assume smu01lem.3: |- ( ( ph /\ ( k e. NN0 /\ n e. NN0 ) ) -> -. ( k e. A /\ ( n - k ) e. B ) )

  disjoint k n
  disjoint A k
  disjoint A n
  disjoint B k
  disjoint B n
  disjoint k ph
  disjoint n ph
  disjoint k m
  disjoint k p
  disjoint k x
  disjoint m n
  disjoint m p
  disjoint m x
  disjoint A m
  disjoint n p
  disjoint n x
  disjoint p x
  disjoint A p
  disjoint A x
  disjoint B m
  disjoint B p
  disjoint B x
  disjoint ph x
  assert |- ( ph -> ( A smul B ) = (/) )

  proof
    wph
    vk
    cA
    cB
    csmu
    co
    #
    wph
    vk
    cv
    #
    @0
    wcel
    #
    wph
    @2
    @1
    cn0
    wcel
    #
    @2
    wn
    #
    wph
    @0
    cn0
    @1
    wph
    cA
    cn0
    wss
    #
    cB
    cn0
    wss
    #
    @0
    cn0
    wss
    smu01lem.1
    smu01lem.2
    cA
    cB
    smucl
    syl2anc
    sseld
    wph
    @3
    @4
    wph
    @3
    wa
    #
    @2
    @1
    @1
    c1
    caddc
    co
    #
    vp
    vm
    cn0
    cpw
    cn0
    vp
    cv
    vm
    cv
    #
    cA
    wcel
    vn
    cv
    #
    @9
    cmin
    co
    cB
    wcel
    wa
    vn
    cn0
    crab
    csad
    co
    cmpt2
    vn
    cn0
    @10
    cc0
    wceq
    c0
    @10
    c1
    cmin
    co
    cif
    cmpt
    cc0
    cseq
    #
    cfv
    #
    wcel
    #
    @7
    @13
    @1
    c0
    wcel
    @1
    noel
    @7
    @12
    c0
    @1
    @3
    wph
    @12
    c0
    wceq
    #
    @3
    @8
    cn0
    wcel
    wph
    @14
    wi
    #
    @1
    peano2nn0
    wph
    vx
    cv
    #
    @11
    cfv
    #
    c0
    wceq
    #
    wi
    wph
    cc0
    @11
    cfv
    #
    c0
    wceq
    #
    wi
    wph
    @1
    @11
    cfv
    #
    c0
    wceq
    #
    wi
    @15
    @15
    vx
    vk
    @8
    @16
    cc0
    wceq
    #
    @18
    @20
    wph
    @23
    @17
    @19
    c0
    @16
    cc0
    @11
    fveq2
    eqeq1d
    imbi2d
    @16
    @1
    wceq
    #
    @18
    @22
    wph
    @24
    @17
    @21
    c0
    @16
    @1
    @11
    fveq2
    eqeq1d
    imbi2d
    @16
    @8
    wceq
    #
    @18
    @14
    wph
    @25
    @17
    @12
    c0
    @16
    @8
    @11
    fveq2
    eqeq1d
    imbi2d
    #
    @26
    wph
    cA
    cB
    @11
    vm
    vn
    vp
    smu01lem.1
    smu01lem.2
    @11
    eqid
    #
    smup0
    @3
    wph
    @22
    @14
    wph
    @3
    @22
    @14
    wi
    @22
    @14
    @7
    @21
    @1
    cA
    wcel
    @10
    @1
    cmin
    co
    cB
    wcel
    wa
    #
    vn
    cn0
    crab
    #
    csad
    co
    #
    c0
    @29
    csad
    co
    #
    wceq
    @21
    c0
    @29
    csad
    oveq1
    @7
    @12
    @30
    c0
    @31
    @7
    cA
    cB
    @11
    vm
    vn
    @1
    vp
    wph
    @5
    @3
    smu01lem.1
    adantr
    #
    wph
    @6
    @3
    smu01lem.2
    adantr
    #
    @27
    wph
    @3
    simpr
    #
    smupp1
    @7
    @31
    c0
    c0
    csad
    co
    #
    c0
    @7
    @29
    c0
    c0
    csad
    @7
    @28
    wn
    #
    vn
    cn0
    wral
    @29
    c0
    wceq
    @7
    @36
    vn
    cn0
    wph
    @3
    @10
    cn0
    wcel
    @36
    smu01lem.3
    anassrs
    ralrimiva
    @28
    vn
    cn0
    rabeq0
    sylibr
    oveq2d
    c0
    cn0
    wss
    @35
    c0
    wceq
    @7
    cn0
    0ss
    c0
    sadid1
    mp1i
    eqtr2d
    eqeq12d
    syl5ibr
    expcom
    a2d
    nn0ind
    syl
    impcom
    eleq2d
    mtbiri
    @7
    cA
    cB
    @11
    vm
    vn
    @1
    vp
    @32
    @33
    @27
    @34
    smuval
    mtbird
    ex
    syld
    pm2.01d
    eq0rdv
end
