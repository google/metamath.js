include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "elfzuz.mm"
include "syl.mm"
include "cv.mm"
include "wss.mm"
include "elfzuz3.mm"
include "fzss2.mm"
include "3syl.mm"
include "sselda.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "wa.mm"
include "cmul.mm"
include "cmpt.mm"
include "cvv.mm"
include "wceq.mm"
include "simprl.mm"
include "simprr.mm"
include "adantr.mm"
include "mptexg.mm"
include "fveq1.mm"
include "oveqan12d.mm"
include "mpteq2dv.mm"
include "ovmpt2ga.mm"
include "syl3anc.mm"
include "w3a.mm"
include "3simpc.mm"
include "wi.mm"
include "eleq1.mm"
include "3anbi2d.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "3anbi3d.mm"
include "oveq2d.mm"
include "vtocl2g.mm"
include "mpcom.mm"
include "3expb.mm"
include "eqeltrd.mm"
include "seqcl.mm"
include "syl5eqel.mm"

theorem fmulcl
  let wph: wff ph
  let vt: setvar t
  let cP: class P
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vh: setvar h
  let vl: setvar l
  assume fmulcl.1: |- P = ( f e. Y , g e. Y |-> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) )
  assume fmulcl.2: |- X = ( seq 1 ( P , U ) ` N )
  assume fmulcl.4: |- ( ph -> N e. ( 1 ... M ) )
  assume fmulcl.5: |- ( ph -> U : ( 1 ... M ) --> Y )
  assume fmulcl.6: |- ( ( ph /\ f e. Y /\ g e. Y ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. Y )
  assume fmulcl.7: |- ( ph -> T e. _V )

  disjoint f g
  disjoint f t
  disjoint T f
  disjoint g t
  disjoint T g
  disjoint T t
  disjoint Y f
  disjoint Y g
  disjoint f ph
  disjoint g ph
  disjoint f h
  disjoint f l
  disjoint g h
  disjoint g l
  disjoint h l
  disjoint h t
  disjoint T h
  disjoint l t
  disjoint T l
  disjoint Y h
  disjoint Y l
  disjoint h ph
  disjoint l ph
  disjoint N h
  disjoint P h
  disjoint P l
  disjoint U h
  disjoint U l
  assert |- ( ph -> X e. Y )

  proof
    wph
    cX
    cN
    cP
    cU
    c1
    cseq
    cfv
    cY
    fmulcl.2
    wph
    vh
    vl
    cP
    cY
    cU
    c1
    cN
    wph
    cN
    c1
    cM
    cfz
    co
    #
    wcel
    #
    cN
    c1
    cuz
    cfv
    wcel
    fmulcl.4
    cN
    c1
    cM
    elfzuz
    syl
    wph
    vh
    cv
    #
    c1
    cN
    cfz
    co
    #
    wcel
    @2
    @0
    wcel
    @2
    cU
    cfv
    cY
    wcel
    wph
    @3
    @0
    @2
    wph
    @1
    cM
    cN
    cuz
    cfv
    wcel
    @3
    @0
    wss
    fmulcl.4
    cN
    c1
    cM
    elfzuz3
    cN
    c1
    cM
    fzss2
    3syl
    sselda
    wph
    @0
    cY
    @2
    cU
    fmulcl.5
    ffvelrnda
    syldan
    wph
    @2
    cY
    wcel
    #
    vl
    cv
    #
    cY
    wcel
    #
    wa
    #
    wa
    #
    @2
    @5
    cP
    co
    #
    vt
    cT
    vt
    cv
    #
    @2
    cfv
    #
    @10
    @5
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cY
    @8
    @4
    @6
    @14
    cvv
    wcel
    #
    @9
    @14
    wceq
    wph
    @4
    @6
    simprl
    wph
    @4
    @6
    simprr
    @8
    cT
    cvv
    wcel
    #
    @15
    wph
    @16
    @7
    fmulcl.7
    adantr
    vt
    cT
    @13
    cvv
    mptexg
    syl
    vf
    vg
    @2
    @5
    cY
    cY
    vt
    cT
    @10
    vf
    cv
    #
    cfv
    #
    @10
    vg
    cv
    #
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    @14
    cP
    cvv
    @17
    @2
    wceq
    #
    @19
    @5
    wceq
    #
    wa
    vt
    cT
    @21
    @13
    @23
    @24
    @18
    @11
    @20
    @12
    cmul
    @10
    @17
    @2
    fveq1
    #
    @10
    @19
    @5
    fveq1
    #
    oveqan12d
    mpteq2dv
    fmulcl.1
    ovmpt2ga
    syl3anc
    wph
    @4
    @6
    @14
    cY
    wcel
    #
    @7
    wph
    @4
    @6
    w3a
    #
    @27
    wph
    @4
    @6
    3simpc
    wph
    @17
    cY
    wcel
    #
    @19
    cY
    wcel
    #
    w3a
    #
    @22
    cY
    wcel
    #
    wi
    wph
    @4
    @30
    w3a
    #
    vt
    cT
    @11
    @20
    cmul
    co
    #
    cmpt
    #
    cY
    wcel
    #
    wi
    @28
    @27
    wi
    vf
    vg
    @2
    @5
    cY
    cY
    @23
    @31
    @33
    @32
    @36
    @23
    @29
    @4
    wph
    @30
    @17
    @2
    cY
    eleq1
    3anbi2d
    @23
    @22
    @35
    cY
    @23
    vt
    cT
    @21
    @34
    @23
    @18
    @11
    @20
    cmul
    @25
    oveq1d
    mpteq2dv
    eleq1d
    imbi12d
    @24
    @33
    @28
    @36
    @27
    @24
    @30
    @6
    wph
    @4
    @19
    @5
    cY
    eleq1
    3anbi3d
    @24
    @35
    @14
    cY
    @24
    vt
    cT
    @34
    @13
    @24
    @20
    @12
    @11
    cmul
    @26
    oveq2d
    mpteq2dv
    eleq1d
    imbi12d
    fmulcl.6
    vtocl2g
    mpcom
    3expb
    eqeltrd
    seqcl
    syl5eqel
end
