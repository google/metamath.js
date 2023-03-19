include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "ci.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "ce.mm"
include "csu.mm"
include "cc.mm"
include "cvts.mm"
include "cvv.mm"
include "cn.mm"
include "cmap.mm"
include "wcel.mm"
include "cn0.mm"
include "cmpt.mm"
include "wceq.mm"
include "wf.mm"
include "cnex.mm"
include "nnex.mm"
include "elmap.mm"
include "sylibr.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "sumeq2sdv.mm"
include "mpteq2dv.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "df-vts.mm"
include "mptex.mm"
include "ovmpt2.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "adantl.mm"
include "sumex.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem vtsval
  let wph: wff ph
  let cL: class L
  let cN: class N
  let cX: class X
  let va: setvar a
  let vl: setvar l
  let vn: setvar n
  let vx: setvar x
  assume vtsval.n: |- ( ph -> N e. NN0 )
  assume vtsval.x: |- ( ph -> X e. CC )
  assume vtsval.l: |- ( ph -> L : NN --> CC )

  disjoint L a
  disjoint N a
  disjoint X a
  disjoint L l
  disjoint L n
  disjoint L x
  disjoint a l
  disjoint a n
  disjoint a x
  disjoint l n
  disjoint l x
  disjoint n x
  disjoint N l
  disjoint N n
  disjoint N x
  disjoint X x
  disjoint ph x
  assert |- ( ph -> ( ( L vts N ) ` X ) = sum_ a e. ( 1 ... N ) ( ( L ` a ) x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( a x. X ) ) ) ) )

  proof
    wph
    vx
    cX
    c1
    cN
    cfz
    co
    #
    va
    cv
    #
    cL
    cfv
    #
    ci
    c2
    cpi
    cmul
    co
    cmul
    co
    #
    @1
    vx
    cv
    #
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    va
    csu
    #
    @0
    @2
    @3
    @1
    cX
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    va
    csu
    #
    cc
    cL
    cN
    cvts
    co
    #
    cvv
    wph
    cL
    cc
    cn
    cmap
    co
    #
    wcel
    #
    cN
    cn0
    wcel
    @15
    vx
    cc
    @9
    cmpt
    #
    wceq
    wph
    cn
    cc
    cL
    wf
    @17
    vtsval.l
    cc
    cn
    cL
    cnex
    nnex
    elmap
    sylibr
    vtsval.n
    vl
    vn
    cL
    cN
    @16
    cn0
    vx
    cc
    c1
    vn
    cv
    #
    cfz
    co
    #
    @1
    vl
    cv
    #
    cfv
    #
    @7
    cmul
    co
    #
    va
    csu
    #
    cmpt
    @18
    cvts
    vx
    cc
    @20
    @8
    va
    csu
    #
    cmpt
    @21
    cL
    wceq
    #
    vx
    cc
    @24
    @25
    @26
    @20
    @23
    @8
    va
    @26
    @22
    @2
    @7
    cmul
    @1
    @21
    cL
    fveq1
    oveq1d
    sumeq2sdv
    mpteq2dv
    @19
    cN
    wceq
    #
    vx
    cc
    @25
    @9
    @27
    @20
    @0
    @8
    va
    @19
    cN
    c1
    cfz
    oveq2
    sumeq1d
    mpteq2dv
    vx
    vn
    va
    vl
    df-vts
    vx
    cc
    @9
    cnex
    mptex
    ovmpt2
    syl2anc
    @4
    cX
    wceq
    #
    @9
    @14
    wceq
    wph
    @28
    @0
    @8
    @13
    va
    @28
    @7
    @12
    @2
    cmul
    @28
    @6
    @11
    ce
    @28
    @5
    @10
    @3
    cmul
    @4
    cX
    @1
    cmul
    oveq2
    oveq2d
    fveq2d
    oveq2d
    sumeq2sdv
    adantl
    vtsval.x
    @14
    cvv
    wcel
    wph
    @0
    @13
    va
    sumex
    a1i
    fvmptd
end
