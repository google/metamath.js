include "csseq.mm"
include "co.mm"
include "cn0.mm"
include "wfn.mm"
include "clsw.mm"
include "cvv.mm"
include "cv.mm"
include "cfv.mm"
include "cs1.mm"
include "cconcat.mm"
include "cmpt2.mm"
include "csn.mm"
include "cxp.mm"
include "chash.mm"
include "cseq.mm"
include "ccom.mm"
include "cun.mm"
include "cc0.mm"
include "cfzo.mm"
include "cuz.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cword.mm"
include "wcel.mm"
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
include "3syl.mm"
include "ssv.mm"
include "fnco.mm"
include "syl3anc.mm"
include "fzouzdisj.mm"
include "fnun.mm"
include "syl21anc.mm"
include "sseqval.mm"
include "nn0uz.mm"
include "elnn0uz.mm"
include "fzouzsplit.mm"
include "sylbi.mm"
include "syl5eq.mm"
include "fneq12d.mm"
include "mpbird.mm"

theorem sseqfn
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cM: class M
  let cW: class W
  let vf: setvar f
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  assume sseqval.1: |- ( ph -> S e. _V )
  assume sseqval.2: |- ( ph -> M e. Word S )
  assume sseqval.3: |- W = ( Word S i^i ( `' # " ( ZZ>= ` ( # ` M ) ) ) )
  assume sseqval.4: |- ( ph -> F : W --> S )


  assert |- ( ph -> ( M seqstr F ) Fn NN0 )

  proof
    wph
    cM
    cF
    csseq
    co
    #
    cn0
    wfn
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
    cc0
    @4
    cfzo
    co
    #
    @4
    cuz
    cfv
    #
    cun
    #
    wfn
    #
    wph
    cM
    @8
    wfn
    #
    @6
    @9
    wfn
    #
    @8
    @9
    cin
    c0
    wceq
    #
    @11
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
    @9
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
    @15
    @4
    cz
    wcel
    @17
    sseqval.2
    @15
    @4
    cS
    cM
    lencl
    #
    nn0zd
    @2
    @3
    @4
    seqfn
    3syl
    @19
    wph
    @18
    ssv
    a1i
    cvv
    @9
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
    @8
    @9
    cM
    @6
    fnun
    syl21anc
    wph
    cn0
    @10
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
    wph
    cn0
    cc0
    cuz
    cfv
    #
    @10
    nn0uz
    wph
    @15
    @4
    cn0
    wcel
    #
    @22
    @10
    wceq
    #
    sseqval.2
    @21
    @23
    @4
    @22
    wcel
    @24
    @4
    elnn0uz
    cc0
    @4
    fzouzsplit
    sylbi
    3syl
    syl5eq
    fneq12d
    mpbird
end
