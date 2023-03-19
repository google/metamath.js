include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cres.mm"
include "chash.mm"
include "cfv.mm"
include "wfn.mm"
include "wceq.mm"
include "cn0.mm"
include "wss.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "fzo0ssnn0.mm"
include "fnssres.mm"
include "sylancl.mm"
include "hashfn.mm"
include "wcel.mm"
include "hashfzo0.mm"
include "eqtrd.mm"

theorem subiwrdlen
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cN: class N
  assume iwrdsplit.s: |- ( ph -> S e. _V )
  assume iwrdsplit.f: |- ( ph -> F : NN0 --> S )
  assume iwrdsplit.n: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( # ` ( F |` ( 0 ..^ N ) ) ) = N )

  proof
    wph
    cF
    cc0
    cN
    cfzo
    co
    #
    cres
    #
    chash
    cfv
    #
    @0
    chash
    cfv
    #
    cN
    wph
    @1
    @0
    wfn
    #
    @2
    @3
    wceq
    wph
    cF
    cn0
    wfn
    #
    @0
    cn0
    wss
    @4
    wph
    cn0
    cS
    cF
    wf
    @5
    iwrdsplit.f
    cn0
    cS
    cF
    ffn
    syl
    cN
    fzo0ssnn0
    cn0
    @0
    cF
    fnssres
    sylancl
    @0
    @1
    hashfn
    syl
    wph
    cN
    cn0
    wcel
    @3
    cN
    wceq
    iwrdsplit.n
    cN
    hashfzo0
    syl
    eqtrd
end
