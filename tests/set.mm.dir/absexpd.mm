include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "cexp.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "absexp.mm"
include "syl2anc.mm"

theorem absexpd
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume abscld.1: |- ( ph -> A e. CC )
  assume absexpd.2: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( abs ` ( A ^ N ) ) = ( ( abs ` A ) ^ N ) )

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
    cabs
    cfv
    cA
    cabs
    cfv
    cN
    cexp
    co
    wceq
    abscld.1
    absexpd.2
    cA
    cN
    absexp
    syl2anc
end
