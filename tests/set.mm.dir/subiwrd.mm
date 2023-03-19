include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cres.mm"
include "wf.mm"
include "cword.mm"
include "wcel.mm"
include "cn0.mm"
include "wss.mm"
include "fzo0ssnn0.mm"
include "fssres.mm"
include "sylancl.mm"
include "iswrdi.mm"
include "syl.mm"

theorem subiwrd
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cN: class N
  assume iwrdsplit.s: |- ( ph -> S e. _V )
  assume iwrdsplit.f: |- ( ph -> F : NN0 --> S )
  assume iwrdsplit.n: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( F |` ( 0 ..^ N ) ) e. Word S )

  proof
    wph
    cc0
    cN
    cfzo
    co
    #
    cS
    cF
    @0
    cres
    #
    wf
    #
    @1
    cS
    cword
    wcel
    wph
    cn0
    cS
    cF
    wf
    @0
    cn0
    wss
    @2
    iwrdsplit.f
    cN
    fzo0ssnn0
    cn0
    cS
    @0
    cF
    fssres
    sylancl
    cS
    cN
    @1
    iswrdi
    syl
end
