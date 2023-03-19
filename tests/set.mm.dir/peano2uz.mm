include "cz.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "simp1.mm"
include "peano2z.mm"
include "3ad2ant2.mm"
include "cr.mm"
include "zre.mm"
include "letrp1.mm"
include "syl3an2.mm"
include "syl3an1.mm"
include "3jca.mm"
include "eluz2.mm"
include "3imtr4i.mm"

theorem peano2uz
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> ( N + 1 ) e. ( ZZ>= ` M ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cN
    cle
    wbr
    #
    w3a
    #
    @0
    cN
    c1
    caddc
    co
    #
    cz
    wcel
    #
    cM
    @4
    cle
    wbr
    #
    w3a
    cN
    cM
    cuz
    cfv
    #
    wcel
    @4
    @7
    wcel
    @3
    @0
    @5
    @6
    @0
    @1
    @2
    simp1
    @1
    @0
    @5
    @2
    cN
    peano2z
    3ad2ant2
    @0
    cM
    cr
    wcel
    #
    @1
    @2
    @6
    cM
    zre
    @1
    @8
    cN
    cr
    wcel
    @2
    @6
    cN
    zre
    cM
    cN
    letrp1
    syl3an2
    syl3an1
    3jca
    cM
    cN
    eluz2
    cM
    @4
    eluz2
    3imtr4i
end
