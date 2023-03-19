include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "cim.mm"
include "cfv.mm"
include "cre.mm"
include "caddc.mm"
include "wceq.mm"
include "immul.mm"
include "syl2anc.mm"

theorem immuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume recld.1: |- ( ph -> A e. CC )
  assume readdd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( Im ` ( A x. B ) ) = ( ( ( Re ` A ) x. ( Im ` B ) ) + ( ( Im ` A ) x. ( Re ` B ) ) ) )

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
    cim
    cfv
    cA
    cre
    cfv
    cB
    cim
    cfv
    cmul
    co
    cA
    cim
    cfv
    cB
    cre
    cfv
    cmul
    co
    caddc
    co
    wceq
    recld.1
    readdd.2
    cA
    cB
    immul
    syl2anc
end
