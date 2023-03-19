include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "cre.mm"
include "cfv.mm"
include "cim.mm"
include "cmin.mm"
include "wceq.mm"
include "remul.mm"
include "syl2anc.mm"

theorem remuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume recld.1: |- ( ph -> A e. CC )
  assume readdd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( Re ` ( A x. B ) ) = ( ( ( Re ` A ) x. ( Re ` B ) ) - ( ( Im ` A ) x. ( Im ` B ) ) ) )

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
    cre
    cfv
    cA
    cre
    cfv
    cB
    cre
    cfv
    cmul
    co
    cA
    cim
    cfv
    cB
    cim
    cfv
    cmul
    co
    cmin
    co
    wceq
    recld.1
    readdd.2
    cA
    cB
    remul
    syl2anc
end
