include "c0.mm"
include "cvoln.mm"
include "cfv.mm"
include "covoln.mm"
include "cc0.mm"
include "cfn.mm"
include "wcel.mm"
include "0fin.mm"
include "a1i.mm"
include "mblvon.mm"
include "vonmblss2.mm"
include "ovn0val.mm"
include "eqtrd.mm"

theorem von0val
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let vx: setvar x
  assume von0val.1: |- ( ph -> A e. dom ( voln ` (/) ) )


  assert |- ( ph -> ( ( voln ` (/) ) ` A ) = 0 )

  proof
    wph
    cA
    c0
    cvoln
    cfv
    cfv
    cA
    c0
    covoln
    cfv
    cfv
    cc0
    wph
    cA
    c0
    c0
    cfn
    wcel
    wph
    0fin
    a1i
    #
    von0val.1
    mblvon
    wph
    cA
    wph
    c0
    cA
    @0
    von0val.1
    vonmblss2
    ovn0val
    eqtrd
end
