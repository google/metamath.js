include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cn0.mm"
include "cdiv.mm"
include "co.mm"
include "cexp.mm"
include "wceq.mm"
include "expdiv.mm"
include "syl121anc.mm"

theorem expdivd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cN: class N
  assume expcld.1: |- ( ph -> A e. CC )
  assume mulexpd.2: |- ( ph -> B e. CC )
  assume sqdivd.3: |- ( ph -> B =/= 0 )
  assume expdivd.3: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( ( A / B ) ^ N ) = ( ( A ^ N ) / ( B ^ N ) ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cB
    cc0
    wne
    cN
    cn0
    wcel
    cA
    cB
    cdiv
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
    cdiv
    co
    wceq
    expcld.1
    mulexpd.2
    sqdivd.3
    expdivd.3
    cA
    cB
    cN
    expdiv
    syl121anc
end
