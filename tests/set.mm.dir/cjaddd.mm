include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cjadd.mm"
include "syl2anc.mm"

theorem cjaddd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume recld.1: |- ( ph -> A e. CC )
  assume readdd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( * ` ( A + B ) ) = ( ( * ` A ) + ( * ` B ) ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    caddc
    co
    ccj
    cfv
    cA
    ccj
    cfv
    cB
    ccj
    cfv
    caddc
    co
    wceq
    recld.1
    readdd.2
    cA
    cB
    cjadd
    syl2anc
end
