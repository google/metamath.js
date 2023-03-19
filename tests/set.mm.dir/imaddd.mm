include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cim.mm"
include "cfv.mm"
include "wceq.mm"
include "imadd.mm"
include "syl2anc.mm"

theorem imaddd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume recld.1: |- ( ph -> A e. CC )
  assume readdd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( Im ` ( A + B ) ) = ( ( Im ` A ) + ( Im ` B ) ) )

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
    cim
    cfv
    cA
    cim
    cfv
    cB
    cim
    cfv
    caddc
    co
    wceq
    recld.1
    readdd.2
    cA
    cB
    imadd
    syl2anc
end
