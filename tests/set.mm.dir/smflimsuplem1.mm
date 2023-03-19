include "cfv.mm"
include "cdm.mm"
include "cuz.mm"
include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cr.mm"
include "wcel.mm"
include "ciin.mm"
include "crab.mm"
include "cvv.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "supeq1i.mm"
include "mpteq2i.mm"
include "a1i.mm"
include "mpteq1d.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "mpteq12dv.mm"
include "eqtrd.mm"
include "fvex.mm"
include "mptex.mm"
include "fvmptd3.mm"
include "dmeqd.mm"
include "xrltso.mm"
include "supex.mm"
include "eqid.mm"
include "dmmpti.mm"
include "cbviinv.mm"
include "eleq2i.mm"
include "eleq1i.mm"
include "anbi12i.mm"
include "rabbia2.mm"
include "iineq1d.mm"
include "eleq2d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rabbidva2.mm"
include "cz.mm"
include "c0.mm"
include "wne.mm"
include "eluzelz2d.mm"
include "uzid.mm"
include "ne0i.mm"
include "3syl.mm"
include "wral.mm"
include "dmex.mm"
include "rgenw.mm"
include "iinexd.mm"
include "rabexd.mm"
include "3eqtrd.mm"
include "wss.mm"
include "ssrab2.mm"
include "syl.mm"
include "ssid.mm"
include "iinssd.mm"
include "sstrd.mm"
include "eqsstrd.mm"

theorem smflimsuplem1
  let wph: wff ph
  let vx: setvar x
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  assume smflimsuplem1.z: |- Z = ( ZZ>= ` M )
  assume smflimsuplem1.e: |- E = ( n e. Z |-> { x e. |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | sup ( ran ( m e. ( ZZ>= ` n ) |-> ( ( F ` m ) ` x ) ) , RR* , < ) e. RR } )
  assume smflimsuplem1.h: |- H = ( n e. Z |-> ( x e. ( E ` n ) |-> sup ( ran ( m e. ( ZZ>= ` n ) |-> ( ( F ` m ) ` x ) ) , RR* , < ) ) )
  assume smflimsuplem1.k: |- ( ph -> K e. Z )

  disjoint E n
  disjoint E x
  disjoint n x
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint m n
  disjoint m x
  disjoint K n
  disjoint K x
  disjoint Z n
  disjoint F j
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint K j
  disjoint k x
  assert |- ( ph -> dom ( H ` K ) C_ dom ( F ` K ) )

  proof
    wph
    cK
    cH
    cfv
    #
    cdm
    #
    vj
    cK
    cuz
    cfv
    #
    vx
    cv
    #
    vj
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cr
    wcel
    #
    vx
    vj
    @2
    @5
    cdm
    #
    ciin
    #
    crab
    #
    cK
    cF
    cfv
    #
    cdm
    #
    wph
    @1
    vx
    cK
    cE
    cfv
    #
    @9
    cmpt
    #
    cdm
    #
    @16
    @13
    wph
    @0
    @17
    wph
    vn
    cK
    vx
    vn
    cv
    #
    cE
    cfv
    #
    vm
    @19
    cuz
    cfv
    #
    @3
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    @17
    cZ
    cH
    cvv
    smflimsuplem1.h
    @19
    cK
    wceq
    #
    @28
    vx
    @20
    vj
    @21
    @6
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    @17
    @28
    @33
    wceq
    @29
    vx
    @20
    @27
    @32
    cxr
    @26
    @31
    clt
    @25
    @30
    vm
    vj
    @21
    @24
    @6
    @22
    @4
    wceq
    #
    @3
    @23
    @5
    @22
    @4
    cF
    fveq2
    #
    fveq1d
    cbvmptv
    rneqi
    supeq1i
    #
    mpteq2i
    a1i
    @29
    vx
    @20
    @32
    @16
    @9
    @19
    cK
    cE
    fveq2
    @29
    cxr
    @31
    @8
    clt
    @29
    @30
    @7
    @29
    vj
    @21
    @2
    @6
    @19
    cK
    cuz
    fveq2
    #
    mpteq1d
    rneqd
    supeq1d
    #
    mpteq12dv
    eqtrd
    smflimsuplem1.k
    @17
    cvv
    wcel
    wph
    vx
    @16
    @9
    cK
    cE
    fvex
    mptex
    a1i
    fvmptd3
    dmeqd
    @18
    @16
    wceq
    wph
    vx
    @16
    @9
    @17
    cxr
    @8
    clt
    xrltso
    supex
    @17
    eqid
    dmmpti
    a1i
    wph
    vn
    cK
    @27
    cr
    wcel
    #
    vx
    vm
    @21
    @23
    cdm
    #
    ciin
    #
    crab
    #
    @13
    cZ
    cE
    cvv
    smflimsuplem1.e
    @29
    @42
    @32
    cr
    wcel
    #
    vx
    vj
    @21
    @11
    ciin
    #
    crab
    #
    @13
    @42
    @45
    wceq
    @29
    @39
    @43
    vx
    @41
    @44
    @3
    @41
    wcel
    @3
    @44
    wcel
    #
    @39
    @43
    @41
    @44
    @3
    vm
    vj
    @21
    @40
    @11
    @34
    @23
    @5
    @35
    dmeqd
    cbviinv
    eleq2i
    @27
    @32
    cr
    @36
    eleq1i
    anbi12i
    rabbia2
    a1i
    @29
    @43
    @10
    vx
    @44
    @12
    @29
    @46
    @3
    @12
    wcel
    @43
    @10
    @29
    @44
    @12
    @3
    @29
    vj
    @21
    @2
    @11
    @37
    iineq1d
    eleq2d
    @29
    @32
    @9
    cr
    @38
    eleq1d
    anbi12d
    rabbidva2
    eqtrd
    smflimsuplem1.k
    wph
    @10
    vx
    @12
    @13
    cvv
    @13
    eqid
    wph
    vj
    @2
    @11
    cvv
    wph
    cK
    cz
    wcel
    #
    cK
    @2
    wcel
    #
    @2
    c0
    wne
    wph
    cM
    cK
    cZ
    smflimsuplem1.z
    smflimsuplem1.k
    eluzelz2d
    #
    cK
    uzid
    #
    @2
    cK
    ne0i
    3syl
    @11
    cvv
    wcel
    #
    vj
    @2
    wral
    wph
    @51
    vj
    @2
    @5
    @4
    cF
    fvex
    dmex
    rgenw
    a1i
    iinexd
    rabexd
    fvmptd3
    3eqtrd
    wph
    @13
    @12
    @15
    @13
    @12
    wss
    wph
    @10
    vx
    @12
    ssrab2
    a1i
    wph
    vj
    @2
    @11
    @15
    @15
    cK
    wph
    @47
    @48
    @49
    @50
    syl
    @4
    cK
    wceq
    @5
    @14
    @4
    cK
    cF
    fveq2
    dmeqd
    @15
    @15
    wss
    wph
    @15
    ssid
    a1i
    iinssd
    sstrd
    eqsstrd
end
