include "csseq.mm"
include "co.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "adantr.mm"
include "cword.mm"
include "wf.mm"
include "simpr.mm"
include "sseqfv1.mm"
include "ralrimiva.mm"
include "cn0.mm"
include "wfn.mm"
include "wss.mm"
include "wb.mm"
include "sseqfn.mm"
include "wrdfn.mm"
include "syl.mm"
include "fzo0ssnn0.mm"
include "a1i.mm"
include "fvreseq1.mm"
include "syl21anc.mm"
include "mpbird.mm"

theorem sseqfres
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cM: class M
  let cW: class W
  let vf: setvar f
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vi: setvar i
  assume sseqval.1: |- ( ph -> S e. _V )
  assume sseqval.2: |- ( ph -> M e. Word S )
  assume sseqval.3: |- W = ( Word S i^i ( `' # " ( ZZ>= ` ( # ` M ) ) ) )
  assume sseqval.4: |- ( ph -> F : W --> S )


  assert |- ( ph -> ( ( M seqstr F ) |` ( 0 ..^ ( # ` M ) ) ) = M )

  proof
    wph
    cM
    cF
    csseq
    co
    #
    cc0
    cM
    chash
    cfv
    #
    cfzo
    co
    #
    cres
    cM
    wceq
    #
    vi
    cv
    #
    @0
    cfv
    @4
    cM
    cfv
    wceq
    #
    vi
    @2
    wral
    #
    wph
    @5
    vi
    @2
    wph
    @4
    @2
    wcel
    #
    wa
    cS
    cF
    cM
    @4
    cW
    wph
    cS
    cvv
    wcel
    @7
    sseqval.1
    adantr
    wph
    cM
    cS
    cword
    wcel
    #
    @7
    sseqval.2
    adantr
    sseqval.3
    wph
    cW
    cS
    cF
    wf
    @7
    sseqval.4
    adantr
    wph
    @7
    simpr
    sseqfv1
    ralrimiva
    wph
    @0
    cn0
    wfn
    cM
    @2
    wfn
    #
    @2
    cn0
    wss
    #
    @3
    @6
    wb
    wph
    cS
    cF
    cM
    cW
    sseqval.1
    sseqval.2
    sseqval.3
    sseqval.4
    sseqfn
    wph
    @8
    @9
    sseqval.2
    cS
    cM
    wrdfn
    syl
    @10
    wph
    @1
    fzo0ssnn0
    a1i
    vi
    cn0
    @2
    @0
    cM
    fvreseq1
    syl21anc
    mpbird
end
