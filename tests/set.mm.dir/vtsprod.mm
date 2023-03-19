include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "cfv.mm"
include "ci.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "ce.mm"
include "cexp.mm"
include "csu.mm"
include "cprod.mm"
include "crepr.mm"
include "cvts.mm"
include "cc.mm"
include "wcel.mm"
include "ax-icn.mm"
include "a1i.mm"
include "2cnd.mm"
include "picn.mm"
include "mulcld.mm"
include "efcld.mm"
include "breprexp.mm"
include "wa.mm"
include "cn0.mm"
include "adantr.mm"
include "cn.mm"
include "cmap.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "elmapi.mm"
include "syl.mm"
include "vtsval.mm"
include "cz.mm"
include "fzssz.mm"
include "simpr.mm"
include "sseldi.mm"
include "zcnd.mm"
include "ad2antrr.mm"
include "mul12d.mm"
include "fveq2d.mm"
include "wceq.mm"
include "efexp.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "sumeq2dv.mm"
include "eqtrd.mm"
include "prodeq2dv.mm"
include "3eqtr4d.mm"

theorem vtsprod
  let wph: wff ph
  let cS: class S
  let vm: setvar m
  let cL: class L
  let cN: class N
  let cX: class X
  let va: setvar a
  let vc: setvar c
  let vb: setvar b
  assume vtsval.n: |- ( ph -> N e. NN0 )
  assume vtsval.x: |- ( ph -> X e. CC )
  assume vtsprod.s: |- ( ph -> S e. NN0 )
  assume vtsprod.l: |- ( ph -> L : ( 0 ..^ S ) --> ( CC ^m NN ) )

  disjoint L a
  disjoint L c
  disjoint L m
  disjoint a c
  disjoint a m
  disjoint c m
  disjoint N a
  disjoint N c
  disjoint N m
  disjoint S a
  disjoint S c
  disjoint S m
  disjoint X a
  disjoint X c
  disjoint X m
  disjoint a ph
  disjoint c ph
  disjoint m ph
  disjoint L b
  disjoint a b
  disjoint b c
  disjoint b m
  disjoint N b
  disjoint S b
  disjoint X b
  disjoint b ph
  assert |- ( ph -> prod_ a e. ( 0 ..^ S ) ( ( ( L ` a ) vts N ) ` X ) = sum_ m e. ( 0 ... ( S x. N ) ) sum_ c e. ( ( 1 ... N ) ( repr ` S ) m ) ( prod_ a e. ( 0 ..^ S ) ( ( L ` a ) ` ( c ` a ) ) x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( m x. X ) ) ) ) )

  proof
    wph
    cc0
    cS
    cfzo
    co
    #
    c1
    cN
    cfz
    co
    #
    vb
    cv
    #
    va
    cv
    #
    cL
    cfv
    #
    cfv
    #
    ci
    c2
    cpi
    cmul
    co
    #
    cmul
    co
    #
    cX
    cmul
    co
    #
    ce
    cfv
    #
    @2
    cexp
    co
    #
    cmul
    co
    #
    vb
    csu
    #
    va
    cprod
    cc0
    cS
    cN
    cmul
    co
    #
    cfz
    co
    #
    @1
    vm
    cv
    #
    cS
    crepr
    cfv
    co
    #
    @0
    @3
    vc
    cv
    #
    cfv
    @4
    cfv
    va
    cprod
    #
    @9
    @15
    cexp
    co
    #
    cmul
    co
    #
    vc
    csu
    #
    vm
    csu
    @0
    cX
    @4
    cN
    cvts
    co
    cfv
    #
    va
    cprod
    @14
    @16
    @18
    @7
    @15
    cX
    cmul
    co
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    vc
    csu
    #
    vm
    csu
    wph
    cS
    vm
    cL
    cN
    @9
    va
    vb
    vc
    vtsval.n
    vtsprod.s
    wph
    @8
    wph
    @7
    cX
    wph
    ci
    @6
    ci
    cc
    wcel
    wph
    ax-icn
    a1i
    wph
    c2
    cpi
    wph
    2cnd
    cpi
    cc
    wcel
    wph
    picn
    a1i
    mulcld
    mulcld
    #
    vtsval.x
    mulcld
    #
    efcld
    vtsprod.l
    breprexp
    wph
    @0
    @22
    @12
    va
    wph
    @3
    @0
    wcel
    #
    wa
    #
    @22
    @1
    @5
    @7
    @2
    cX
    cmul
    co
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    vb
    csu
    @12
    @30
    @4
    cN
    cX
    vb
    wph
    cN
    cn0
    wcel
    @29
    vtsval.n
    adantr
    wph
    cX
    cc
    wcel
    #
    @29
    vtsval.x
    adantr
    #
    @30
    @4
    cc
    cn
    cmap
    co
    #
    wcel
    cn
    cc
    @4
    wf
    wph
    @0
    @36
    @3
    cL
    vtsprod.l
    ffvelrnda
    @4
    cc
    cn
    elmapi
    syl
    vtsval
    @30
    @1
    @33
    @11
    vb
    @30
    @2
    @1
    wcel
    #
    wa
    #
    @32
    @10
    @5
    cmul
    @38
    @2
    @8
    cmul
    co
    #
    ce
    cfv
    #
    @32
    @10
    @38
    @39
    @31
    ce
    @38
    @2
    @7
    cX
    @38
    @2
    @38
    @1
    cz
    @2
    c1
    cN
    fzssz
    @30
    @37
    simpr
    sseldi
    #
    zcnd
    wph
    @7
    cc
    wcel
    #
    @29
    @37
    @27
    ad2antrr
    @30
    @34
    @37
    @35
    adantr
    mul12d
    fveq2d
    @38
    @8
    cc
    wcel
    #
    @2
    cz
    wcel
    @40
    @10
    wceq
    wph
    @43
    @29
    @37
    @28
    ad2antrr
    @41
    @8
    @2
    efexp
    syl2anc
    eqtr3d
    oveq2d
    sumeq2dv
    eqtrd
    prodeq2dv
    wph
    @14
    @26
    @21
    vm
    wph
    @15
    @14
    wcel
    #
    wa
    #
    @16
    @25
    @20
    vc
    @45
    @17
    @16
    wcel
    #
    wa
    #
    @24
    @19
    @18
    cmul
    @47
    @15
    @8
    cmul
    co
    #
    ce
    cfv
    #
    @24
    @19
    @47
    @48
    @23
    ce
    @47
    @15
    @7
    cX
    @47
    @15
    @45
    @15
    cz
    wcel
    #
    @46
    @45
    @14
    cz
    @15
    cc0
    @13
    fzssz
    wph
    @44
    simpr
    sseldi
    adantr
    #
    zcnd
    wph
    @42
    @44
    @46
    @27
    ad2antrr
    wph
    @34
    @44
    @46
    vtsval.x
    ad2antrr
    mul12d
    fveq2d
    @47
    @43
    @50
    @49
    @19
    wceq
    wph
    @43
    @44
    @46
    @28
    ad2antrr
    @51
    @8
    @15
    efexp
    syl2anc
    eqtr3d
    oveq2d
    sumeq2dv
    sumeq2dv
    3eqtr4d
end
