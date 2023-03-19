include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "ccxp.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "wceq.mm"
include "logcxp.mm"
include "syl2anc.mm"

theorem logcxpd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpcxpcld.1: |- ( ph -> A e. RR+ )
  assume rpcxpcld.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( log ` ( A ^c B ) ) = ( B x. ( log ` A ) ) )

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
    clog
    cfv
    cB
    cA
    clog
    cfv
    cmul
    co
    wceq
    rpcxpcld.1
    rpcxpcld.2
    cA
    cB
    logcxp
    syl2anc
end
