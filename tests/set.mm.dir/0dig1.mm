include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cdig.mm"
include "co.mm"
include "wceq.mm"
include "cif.mm"
include "cz.mm"
include "0z.mm"
include "dig1.mm"
include "mpan2.mm"
include "eqid.mm"
include "iftruei.mm"
include "syl6eq.mm"

theorem 0dig1
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( B e. ( ZZ>= ` 2 ) -> ( 0 ( digit ` B ) 1 ) = 1 )

  proof
    cB
    c2
    cuz
    cfv
    wcel
    #
    cc0
    c1
    cB
    cdig
    cfv
    co
    #
    cc0
    cc0
    wceq
    #
    c1
    cc0
    cif
    #
    c1
    @0
    cc0
    cz
    wcel
    @1
    @3
    wceq
    0z
    cB
    cc0
    dig1
    mpan2
    @2
    c1
    cc0
    cc0
    eqid
    iftruei
    syl6eq
end
