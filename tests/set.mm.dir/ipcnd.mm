include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cre.mm"
include "cim.mm"
include "caddc.mm"
include "wceq.mm"
include "ipcnval.mm"
include "syl2anc.mm"

theorem ipcnd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume recld.1: |- ( ph -> A e. CC )
  assume readdd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( Re ` ( A x. ( * ` B ) ) ) = ( ( ( Re ` A ) x. ( Re ` B ) ) + ( ( Im ` A ) x. ( Im ` B ) ) ) )

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
    ccj
    cfv
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
    caddc
    co
    wceq
    recld.1
    readdd.2
    cA
    cB
    ipcnval
    syl2anc
end
