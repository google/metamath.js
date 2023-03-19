include "csseq.mm"
include "co.mm"
include "cfv.mm"
include "clsw.mm"
include "cvv.mm"
include "cv.mm"
include "cs1.mm"
include "cconcat.mm"
include "cmpt2.mm"
include "cn0.mm"
include "csn.mm"
include "cxp.mm"
include "chash.mm"
include "cseq.mm"
include "ccom.mm"
include "cun.mm"
include "sseqval.mm"
include "fveq1d.mm"
include "cc0.mm"
include "cfzo.mm"
include "wfn.mm"
include "cuz.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "cword.mm"
include "wrdfn.mm"
include "syl.mm"
include "crn.mm"
include "wss.mm"
include "c1.mm"
include "cmin.mm"
include "fvex.mm"
include "df-lsw.mm"
include "fnmpti.mm"
include "a1i.mm"
include "cz.mm"
include "lencl.mm"
include "nn0zd.mm"
include "seqfn.mm"
include "ssv.mm"
include "fnco.mm"
include "syl3anc.mm"
include "fzouzdisj.mm"
include "fvun2.mm"
include "syl112anc.mm"
include "wfun.mm"
include "cdm.mm"
include "fnfun.mm"
include "wf.mm"
include "fvexd.mm"
include "wa.mm"
include "ovexd.mm"
include "eqid.mm"
include "caddc.mm"
include "seqf2.mm"
include "fdm.mm"
include "eleqtrrd.mm"
include "fvco.mm"
include "syl2anc.mm"
include "3eqtrd.mm"

theorem sseqfv2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cF: class F
  let cM: class M
  let cN: class N
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vm: setvar m
  let vw: setvar w
  let vi: setvar i
  assume sseqval.1: |- ( ph -> S e. _V )
  assume sseqval.2: |- ( ph -> M e. Word S )
  assume sseqval.3: |- W = ( Word S i^i ( `' # " ( ZZ>= ` ( # ` M ) ) ) )
  assume sseqval.4: |- ( ph -> F : W --> S )
  assume sseqfv2.4: |- ( ph -> N e. ( ZZ>= ` ( # ` M ) ) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint M x
  disjoint M y
  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint M x
  disjoint M y
  disjoint ph x
  disjoint ph y
  disjoint W x
  disjoint W y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint F a
  disjoint b x
  disjoint b y
  disjoint F b
  disjoint M a
  disjoint M b
  disjoint a ph
  disjoint b ph
  disjoint f m
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint m x
  disjoint m y
  disjoint F m
  disjoint M f
  disjoint M m
  disjoint f ph
  disjoint m ph
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint F a
  disjoint b x
  disjoint b y
  disjoint F b
  disjoint M a
  disjoint M b
  disjoint S w
  disjoint a w
  disjoint W a
  disjoint b w
  disjoint W b
  disjoint w x
  disjoint w y
  disjoint W w
  disjoint a ph
  disjoint b ph
  disjoint ph w
  disjoint F i
  disjoint M i
  disjoint S i
  disjoint i ph
  assert |- ( ph -> ( ( M seqstr F ) ` N ) = ( lastS ` ( seq ( # ` M ) ( ( x e. _V , y e. _V |-> ( x ++ <" ( F ` x ) "> ) ) , ( NN0 X. { ( M ++ <" ( F ` M ) "> ) } ) ) ` N ) ) )

  proof
    wph
    cN
    cM
    cF
    csseq
    co
    #
    cfv
    cN
    cM
    clsw
    vx
    vy
    cvv
    cvv
    vx
    cv
    #
    @1
    cF
    cfv
    cs1
    cconcat
    co
    cmpt2
    #
    cn0
    cM
    cM
    cF
    cfv
    cs1
    cconcat
    co
    csn
    cxp
    #
    cM
    chash
    cfv
    #
    cseq
    #
    ccom
    #
    cun
    #
    cfv
    #
    cN
    @6
    cfv
    #
    cN
    @5
    cfv
    clsw
    cfv
    #
    wph
    cN
    @0
    @7
    wph
    vx
    vy
    cS
    cF
    cM
    cW
    sseqval.1
    sseqval.2
    sseqval.3
    sseqval.4
    sseqval
    fveq1d
    wph
    cM
    cc0
    @4
    cfzo
    co
    #
    wfn
    #
    @6
    @4
    cuz
    cfv
    #
    wfn
    #
    @11
    @13
    cin
    c0
    wceq
    #
    cN
    @13
    wcel
    @8
    @9
    wceq
    wph
    cM
    cS
    cword
    wcel
    #
    @12
    sseqval.2
    cS
    cM
    wrdfn
    syl
    wph
    clsw
    cvv
    wfn
    #
    @5
    @13
    wfn
    #
    @5
    crn
    #
    cvv
    wss
    #
    @14
    @17
    wph
    vx
    cvv
    @1
    chash
    cfv
    c1
    cmin
    co
    #
    @1
    cfv
    clsw
    @21
    @1
    fvex
    vx
    df-lsw
    fnmpti
    a1i
    wph
    @4
    cz
    wcel
    @18
    wph
    @4
    wph
    @16
    @4
    cn0
    wcel
    sseqval.2
    cS
    cM
    lencl
    syl
    nn0zd
    #
    @2
    @3
    @4
    seqfn
    syl
    #
    @20
    wph
    @19
    ssv
    a1i
    cvv
    @13
    clsw
    @5
    fnco
    syl3anc
    @15
    wph
    cc0
    @4
    fzouzdisj
    a1i
    sseqfv2.4
    @11
    @13
    cM
    @6
    cN
    fvun2
    syl112anc
    wph
    @5
    wfun
    #
    cN
    @5
    cdm
    #
    wcel
    @9
    @10
    wceq
    wph
    @18
    @24
    @23
    @13
    @5
    fnfun
    syl
    wph
    cN
    @13
    @25
    sseqfv2.4
    wph
    @13
    cvv
    @5
    wf
    @25
    @13
    wceq
    wph
    va
    vb
    cvv
    cvv
    @2
    @3
    @4
    @13
    wph
    @4
    @3
    fvexd
    wph
    va
    cv
    #
    cvv
    wcel
    vb
    cv
    #
    cvv
    wcel
    wa
    wa
    @26
    @27
    @2
    ovexd
    @13
    eqid
    @22
    wph
    @26
    @4
    c1
    caddc
    co
    cuz
    cfv
    wcel
    wa
    @26
    @3
    fvexd
    seqf2
    @13
    cvv
    @5
    fdm
    syl
    eleqtrrd
    cN
    clsw
    @5
    fvco
    syl2anc
    3eqtrd
end
