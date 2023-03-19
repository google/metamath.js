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
include "fvun1.mm"
include "syl112anc.mm"
include "eqtrd.mm"

theorem sseqfv1
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cM: class M
  let cN: class N
  let cW: class W
  let vf: setvar f
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  assume sseqval.1: |- ( ph -> S e. _V )
  assume sseqval.2: |- ( ph -> M e. Word S )
  assume sseqval.3: |- W = ( Word S i^i ( `' # " ( ZZ>= ` ( # ` M ) ) ) )
  assume sseqval.4: |- ( ph -> F : W --> S )
  assume sseqfv1.4: |- ( ph -> N e. ( 0 ..^ ( # ` M ) ) )


  assert |- ( ph -> ( ( M seqstr F ) ` N ) = ( M ` N ) )

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
    cM
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
    @10
    @12
    cin
    c0
    wceq
    #
    cN
    @10
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
    @11
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
    @12
    wfn
    #
    @5
    crn
    #
    cvv
    wss
    #
    @13
    @16
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
    @20
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
    @17
    wph
    @4
    wph
    @15
    @4
    cn0
    wcel
    sseqval.2
    cS
    cM
    lencl
    syl
    nn0zd
    @2
    @3
    @4
    seqfn
    syl
    @19
    wph
    @18
    ssv
    a1i
    cvv
    @12
    clsw
    @5
    fnco
    syl3anc
    @14
    wph
    cc0
    @4
    fzouzdisj
    a1i
    sseqfv1.4
    @10
    @12
    cM
    @6
    cN
    fvun1
    syl112anc
    eqtrd
end
