include "cv.mm"
include "csn.mm"
include "cun.mm"
include "wcel.mm"
include "cz.mm"
include "wral.mm"
include "csb.mm"
include "vsnid.mm"
include "elun2.mm"
include "ax-mp.mm"
include "rspcsbela.mm"
include "mpan.mm"

theorem modfsummodslem1
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cN: class N

  disjoint A k
  disjoint k z
  disjoint N k
  assert |- ( A. k e. ( A u. { z } ) B e. ZZ -> [_ z / k ]_ B e. ZZ )

  proof
    vz
    cv
    #
    cA
    @0
    csn
    #
    cun
    #
    wcel
    #
    cB
    cz
    wcel
    vk
    @2
    wral
    vk
    @0
    cB
    csb
    cz
    wcel
    @0
    @1
    wcel
    @3
    vz
    vsnid
    @0
    @1
    cA
    elun2
    ax-mp
    vk
    @0
    @2
    cB
    cz
    rspcsbela
    mpan
end
