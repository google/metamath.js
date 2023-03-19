include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "cexp.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cjexp.mm"
include "syl2anc.mm"

theorem cjexpd
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume recld.1: |- ( ph -> A e. CC )
  assume cjexpd.2: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( * ` ( A ^ N ) ) = ( ( * ` A ) ^ N ) )

  proof
    wph
    cA
    cc
    wcel
    cN
    cn0
    wcel
    cA
    cN
    cexp
    co
    ccj
    cfv
    cA
    ccj
    cfv
    cN
    cexp
    co
    wceq
    recld.1
    cjexpd.2
    cA
    cN
    cjexp
    syl2anc
end
