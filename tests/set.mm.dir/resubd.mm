include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "resub.mm"
include "syl2anc.mm"

theorem resubd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume recld.1: |- ( ph -> A e. CC )
  assume readdd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( Re ` ( A - B ) ) = ( ( Re ` A ) - ( Re ` B ) ) )

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
    cmin
    co
    cre
    cfv
    cA
    cre
    cfv
    cB
    cre
    cfv
    cmin
    co
    wceq
    recld.1
    readdd.2
    cA
    cB
    resub
    syl2anc
end
