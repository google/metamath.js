include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "wceq.mm"
include "expadd.mm"
include "syl3anc.mm"

theorem expaddd
  let wph: wff ph
  let cA: class A
  let cM: class M
  let cN: class N
  assume expcld.1: |- ( ph -> A e. CC )
  assume expcld.2: |- ( ph -> N e. NN0 )
  assume expaddd.2: |- ( ph -> M e. NN0 )


  assert |- ( ph -> ( A ^ ( M + N ) ) = ( ( A ^ M ) x. ( A ^ N ) ) )

  proof
    wph
    cA
    cc
    wcel
    cM
    cn0
    wcel
    cN
    cn0
    wcel
    cA
    cM
    cN
    caddc
    co
    cexp
    co
    cA
    cM
    cexp
    co
    cA
    cN
    cexp
    co
    cmul
    co
    wceq
    expcld.1
    expaddd.2
    expcld.2
    cA
    cM
    cN
    expadd
    syl3anc
end
