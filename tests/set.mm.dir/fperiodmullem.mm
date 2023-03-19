include "cn0.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "recnd.mm"
include "mul02d.mm"
include "addid1d.mm"
include "eqtrd.mm"
include "w3a.mm"
include "simp3.mm"
include "simp1.mm"
include "wa.mm"
include "simpr.mm"
include "simpl.mm"
include "mpd.mm"
include "3adant1.mm"
include "cc.mm"
include "nn0cn.mm"
include "adantl.mm"
include "1cnd.mm"
include "adantr.mm"
include "adddird.mm"
include "mulcld.mm"
include "addassd.mm"
include "mulid2d.mm"
include "3eqtr2d.mm"
include "3adant3.mm"
include "cr.mm"
include "nn0re.mm"
include "remulcld.mm"
include "readdcld.mm"
include "ex.mm"
include "imdistani.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "sylc.mm"
include "3eqtrd.mm"
include "syl3anc.mm"
include "3exp.mm"
include "nn0ind.mm"
include "mpcom.mm"

theorem fperiodmullem
  let wph: wff ph
  let vx: setvar x
  let cT: class T
  let cF: class F
  let cN: class N
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  assume fperiodmullem.f: |- ( ph -> F : RR --> CC )
  assume fperiodmullem.t: |- ( ph -> T e. RR )
  assume fperiodmullem.n: |- ( ph -> N e. NN0 )
  assume fperiodmullem.x: |- ( ph -> X e. RR )
  assume fperiodmullem.per: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )

  disjoint F x
  disjoint T x
  disjoint X x
  disjoint ph x
  disjoint F m
  disjoint F n
  disjoint m n
  disjoint m x
  disjoint N n
  disjoint T m
  disjoint T n
  disjoint X m
  disjoint X n
  disjoint m ph
  disjoint n ph
  assert |- ( ph -> ( F ` ( X + ( N x. T ) ) ) = ( F ` X ) )

  proof
    cN
    cn0
    wcel
    wph
    cX
    cN
    cT
    cmul
    co
    #
    caddc
    co
    #
    cF
    cfv
    #
    cX
    cF
    cfv
    #
    wceq
    #
    fperiodmullem.n
    wph
    cX
    vn
    cv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    cF
    cfv
    #
    @3
    wceq
    #
    wi
    wph
    cX
    cc0
    cT
    cmul
    co
    #
    caddc
    co
    #
    cF
    cfv
    #
    @3
    wceq
    #
    wi
    wph
    cX
    vm
    cv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    cF
    cfv
    #
    @3
    wceq
    #
    wi
    #
    wph
    cX
    @14
    c1
    caddc
    co
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    cF
    cfv
    #
    @3
    wceq
    #
    wi
    wph
    @4
    wi
    vn
    vm
    cN
    @5
    cc0
    wceq
    #
    @9
    @13
    wph
    @25
    @8
    @12
    @3
    @25
    @7
    @11
    cF
    @25
    @6
    @10
    cX
    caddc
    @5
    cc0
    cT
    cmul
    oveq1
    oveq2d
    fveq2d
    eqeq1d
    imbi2d
    @5
    @14
    wceq
    #
    @9
    @18
    wph
    @26
    @8
    @17
    @3
    @26
    @7
    @16
    cF
    @26
    @6
    @15
    cX
    caddc
    @5
    @14
    cT
    cmul
    oveq1
    oveq2d
    fveq2d
    eqeq1d
    imbi2d
    @5
    @20
    wceq
    #
    @9
    @24
    wph
    @27
    @8
    @23
    @3
    @27
    @7
    @22
    cF
    @27
    @6
    @21
    cX
    caddc
    @5
    @20
    cT
    cmul
    oveq1
    oveq2d
    fveq2d
    eqeq1d
    imbi2d
    @5
    cN
    wceq
    #
    @9
    @4
    wph
    @28
    @8
    @2
    @3
    @28
    @7
    @1
    cF
    @28
    @6
    @0
    cX
    caddc
    @5
    cN
    cT
    cmul
    oveq1
    oveq2d
    fveq2d
    eqeq1d
    imbi2d
    wph
    @11
    cX
    cF
    wph
    @11
    cX
    cc0
    caddc
    co
    cX
    wph
    @10
    cc0
    cX
    caddc
    wph
    cT
    wph
    cT
    fperiodmullem.t
    recnd
    #
    mul02d
    oveq2d
    wph
    cX
    wph
    cX
    fperiodmullem.x
    recnd
    #
    addid1d
    eqtrd
    fveq2d
    @14
    cn0
    wcel
    #
    @19
    wph
    @24
    @31
    @19
    wph
    w3a
    wph
    @31
    @18
    @24
    @31
    @19
    wph
    simp3
    @31
    @19
    wph
    simp1
    @19
    wph
    @18
    @31
    @19
    wph
    wa
    wph
    @18
    @19
    wph
    simpr
    @19
    wph
    simpl
    mpd
    3adant1
    wph
    @31
    @18
    w3a
    @23
    @16
    cT
    caddc
    co
    #
    cF
    cfv
    #
    @17
    @3
    wph
    @31
    @23
    @33
    wceq
    @18
    wph
    @31
    wa
    #
    @22
    @32
    cF
    @34
    @22
    cX
    @15
    c1
    cT
    cmul
    co
    #
    caddc
    co
    #
    caddc
    co
    @16
    @35
    caddc
    co
    @32
    @34
    @21
    @36
    cX
    caddc
    @34
    @14
    c1
    cT
    @31
    @14
    cc
    wcel
    wph
    @14
    nn0cn
    adantl
    #
    @34
    1cnd
    #
    wph
    cT
    cc
    wcel
    @31
    @29
    adantr
    #
    adddird
    oveq2d
    @34
    cX
    @15
    @35
    wph
    cX
    cc
    wcel
    @31
    @30
    adantr
    @34
    @14
    cT
    @37
    @39
    mulcld
    @34
    c1
    cT
    @38
    @39
    mulcld
    addassd
    @34
    @35
    cT
    @16
    caddc
    @34
    cT
    @39
    mulid2d
    oveq2d
    3eqtr2d
    fveq2d
    3adant3
    wph
    @31
    @33
    @17
    wceq
    #
    @18
    @34
    @16
    cr
    wcel
    #
    wph
    @41
    wa
    #
    @40
    @34
    cX
    @15
    wph
    cX
    cr
    wcel
    @31
    fperiodmullem.x
    adantr
    @34
    @14
    cT
    @31
    @14
    cr
    wcel
    wph
    @14
    nn0re
    adantl
    wph
    cT
    cr
    wcel
    @31
    fperiodmullem.t
    adantr
    remulcld
    readdcld
    #
    wph
    @31
    @41
    wph
    @31
    @41
    @43
    ex
    imdistani
    wph
    vx
    cv
    #
    cr
    wcel
    #
    wa
    #
    @44
    cT
    caddc
    co
    #
    cF
    cfv
    #
    @44
    cF
    cfv
    #
    wceq
    #
    wi
    @42
    @40
    wi
    vx
    @16
    cr
    @44
    @16
    wceq
    #
    @46
    @42
    @50
    @40
    @51
    @45
    @41
    wph
    @44
    @16
    cr
    eleq1
    anbi2d
    @51
    @48
    @33
    @49
    @17
    @51
    @47
    @32
    cF
    @44
    @16
    cT
    caddc
    oveq1
    fveq2d
    @44
    @16
    cF
    fveq2
    eqeq12d
    imbi12d
    fperiodmullem.per
    vtoclg
    sylc
    3adant3
    wph
    @31
    @18
    simp3
    3eqtrd
    syl3anc
    3exp
    nn0ind
    mpcom
end
