include "cin.mm"
include "crepr.mm"
include "cfv.mm"
include "co.mm"
include "c1.mm"
include "csu.mm"
include "chash.mm"
include "cmul.mm"
include "cc0.mm"
include "cfzo.mm"
include "cv.mm"
include "cn.mm"
include "cind.mm"
include "cprod.mm"
include "cfn.mm"
include "wcel.mm"
include "cc.mm"
include "wceq.mm"
include "reprfi.mm"
include "wss.mm"
include "inss2.mm"
include "a1i.mm"
include "reprss.mm"
include "ssfid.mm"
include "1cnd.mm"
include "fsumconst.mm"
include "syl2anc.mm"
include "cif.mm"
include "wral.mm"
include "cuz.mm"
include "wo.mm"
include "ralrimivw.mm"
include "olcd.mm"
include "sumss2.mm"
include "syl21anc.mm"
include "wa.mm"
include "crn.mm"
include "wb.mm"
include "wi.mm"
include "reprinrn.mm"
include "incom.mm"
include "oveq1i.mm"
include "eleq2i.mm"
include "bibi1i.mm"
include "imbi2i.mm"
include "mpbi.mm"
include "baibd.mm"
include "ifbid.mm"
include "cvv.mm"
include "nnex.mm"
include "r19.21bi.mm"
include "fzofi.mm"
include "adantr.mm"
include "cz.mm"
include "cn0.mm"
include "simpr.mm"
include "reprf.mm"
include "fssd.mm"
include "prodindf.mm"
include "eqtr4d.mm"
include "sumeq2dv.mm"
include "eqtrd.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0cnd.mm"
include "mulid1d.mm"
include "3eqtr3rd.mm"

theorem hashreprin
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  let va: setvar a
  let vc: setvar c
  let vb: setvar b
  let vm: setvar m
  let vs: setvar s
  assume reprval.a: |- ( ph -> A C_ NN )
  assume reprval.m: |- ( ph -> M e. ZZ )
  assume reprval.s: |- ( ph -> S e. NN0 )
  assume hashreprin.b: |- ( ph -> B e. Fin )
  assume hashreprin.1: |- ( ph -> B C_ NN )

  disjoint A a
  disjoint B a
  disjoint B c
  disjoint a c
  disjoint M a
  disjoint S a
  disjoint a ph
  disjoint A c
  disjoint M c
  disjoint S a
  disjoint S c
  disjoint a c
  disjoint c ph
  disjoint A b
  disjoint A m
  disjoint b c
  disjoint b m
  disjoint c m
  disjoint M b
  disjoint M m
  disjoint S b
  disjoint S m
  disjoint S s
  disjoint a b
  disjoint a m
  disjoint a s
  disjoint b s
  disjoint c s
  disjoint m s
  disjoint b ph
  disjoint m ph
  disjoint ph s
  assert |- ( ph -> ( # ` ( ( A i^i B ) ( repr ` S ) M ) ) = sum_ c e. ( B ( repr ` S ) M ) prod_ a e. ( 0 ..^ S ) ( ( ( _Ind ` NN ) ` A ) ` ( c ` a ) ) )

  proof
    wph
    cA
    cB
    cin
    #
    cM
    cS
    crepr
    cfv
    #
    co
    #
    c1
    vc
    csu
    #
    @2
    chash
    cfv
    #
    c1
    cmul
    co
    #
    cB
    cM
    @1
    co
    #
    cc0
    cS
    cfzo
    co
    #
    va
    cv
    vc
    cv
    #
    cfv
    cA
    cn
    cind
    cfv
    cfv
    cfv
    va
    cprod
    #
    vc
    csu
    #
    @4
    wph
    @2
    cfn
    wcel
    #
    c1
    cc
    wcel
    #
    @3
    @5
    wceq
    wph
    @6
    @2
    wph
    cB
    cS
    cM
    hashreprin.1
    reprval.m
    reprval.s
    hashreprin.b
    reprfi
    #
    wph
    cB
    @0
    cS
    cM
    hashreprin.1
    reprval.m
    reprval.s
    @0
    cB
    wss
    wph
    cA
    cB
    inss2
    a1i
    reprss
    #
    ssfid
    #
    wph
    1cnd
    #
    @2
    c1
    vc
    fsumconst
    syl2anc
    wph
    @3
    @6
    @8
    @2
    wcel
    #
    c1
    cc0
    cif
    #
    vc
    csu
    #
    @10
    wph
    @2
    @6
    wss
    @12
    vc
    @2
    wral
    @6
    cc0
    cuz
    cfv
    wss
    #
    @6
    cfn
    wcel
    #
    wo
    @3
    @19
    wceq
    @14
    wph
    @12
    vc
    @2
    @16
    ralrimivw
    wph
    @21
    @20
    @13
    olcd
    @2
    @6
    c1
    vc
    cc0
    sumss2
    syl21anc
    wph
    @6
    @18
    @9
    vc
    wph
    @8
    @6
    wcel
    #
    wa
    #
    @18
    @8
    crn
    cA
    wss
    #
    c1
    cc0
    cif
    @9
    @23
    @17
    @24
    c1
    cc0
    wph
    @17
    @22
    @24
    wph
    @8
    cB
    cA
    cin
    #
    cM
    @1
    co
    #
    wcel
    #
    @22
    @24
    wa
    #
    wb
    #
    wi
    wph
    @17
    @28
    wb
    #
    wi
    wph
    cB
    cA
    cS
    cM
    vc
    hashreprin.1
    reprval.m
    reprval.s
    reprinrn
    @29
    @30
    wph
    @27
    @17
    @28
    @26
    @2
    @8
    @25
    @0
    cM
    @1
    cB
    cA
    incom
    oveq1i
    eleq2i
    bibi1i
    imbi2i
    mpbi
    baibd
    ifbid
    @23
    @7
    cA
    va
    @8
    cn
    cvv
    wph
    cn
    cvv
    wcel
    #
    vc
    @6
    wph
    @31
    vc
    @6
    @31
    wph
    nnex
    a1i
    ralrimivw
    r19.21bi
    @7
    cfn
    wcel
    @23
    cc0
    cS
    fzofi
    a1i
    wph
    cA
    cn
    wss
    @22
    reprval.a
    adantr
    @23
    @7
    cB
    cn
    @8
    @23
    cB
    @8
    cS
    cM
    wph
    cB
    cn
    wss
    @22
    hashreprin.1
    adantr
    #
    wph
    cM
    cz
    wcel
    @22
    reprval.m
    adantr
    wph
    cS
    cn0
    wcel
    @22
    reprval.s
    adantr
    wph
    @22
    simpr
    reprf
    @32
    fssd
    prodindf
    eqtr4d
    sumeq2dv
    eqtrd
    wph
    @4
    wph
    @4
    wph
    @11
    @4
    cn0
    wcel
    @15
    @2
    hashcl
    syl
    nn0cnd
    mulid1d
    3eqtr3rd
end
