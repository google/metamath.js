include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "cmul.mm"
include "co.mm"
include "cexp.mm"
include "wceq.mm"
include "mulexp.mm"
include "syl3anc.mm"

theorem mulexpd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cN: class N
  assume expcld.1: |- ( ph -> A e. CC )
  assume mulexpd.2: |- ( ph -> B e. CC )
  assume mulexpd.3: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( ( A x. B ) ^ N ) = ( ( A ^ N ) x. ( B ^ N ) ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cN
    cn0
    wcel
    cA
    cB
    cmul
    co
    cN
    cexp
    co
    cA
    cN
    cexp
    co
    cB
    cN
    cexp
    co
    cmul
    co
    wceq
    expcld.1
    mulexpd.2
    mulexpd.3
    cA
    cB
    cN
    mulexp
    syl3anc
end
