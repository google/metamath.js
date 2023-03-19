include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "ccxp.mm"
include "co.mm"
include "rpcxpcl.mm"
include "syl2anc.mm"

theorem rpcxpcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpcxpcld.1: |- ( ph -> A e. RR+ )
  assume rpcxpcld.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A ^c B ) e. RR+ )

  proof
    wph
    cA
    crp
    wcel
    cB
    cr
    wcel
    cA
    cB
    ccxp
    co
    crp
    wcel
    rpcxpcld.1
    rpcxpcld.2
    cA
    cB
    rpcxpcl
    syl2anc
end
