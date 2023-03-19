include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "readd.mm"
include "syl2anc.mm"

theorem readdd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume recld.1: |- ( ph -> A e. CC )
  assume readdd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( Re ` ( A + B ) ) = ( ( Re ` A ) + ( Re ` B ) ) )

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
    cre
    cfv
    cA
    cre
    cfv
    cB
    cre
    cfv
    caddc
    co
    wceq
    recld.1
    readdd.2
    cA
    cB
    readd
    syl2anc
end
