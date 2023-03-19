include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cjmul.mm"
include "syl2anc.mm"

theorem cjmuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume recld.1: |- ( ph -> A e. CC )
  assume readdd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( * ` ( A x. B ) ) = ( ( * ` A ) x. ( * ` B ) ) )

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
    cmul
    co
    ccj
    cfv
    cA
    ccj
    cfv
    cB
    ccj
    cfv
    cmul
    co
    wceq
    recld.1
    readdd.2
    cA
    cB
    cjmul
    syl2anc
end
