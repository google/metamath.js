include "cz.mm"
include "wcel.mm"
include "cc.mm"
include "cre.mm"
include "cfv.mm"
include "cim.mm"
include "cgz.mm"
include "zcn.mm"
include "zre.mm"
include "rered.mm"
include "id.mm"
include "eqeltrd.mm"
include "cc0.mm"
include "reim0d.mm"
include "0z.mm"
include "syl6eqel.mm"
include "elgz.mm"
include "syl3anbrc.mm"

theorem zgz
  let cA: class A


  assert |- ( A e. ZZ -> A e. Z[i] )

  proof
    cA
    cz
    wcel
    #
    cA
    cc
    wcel
    cA
    cre
    cfv
    #
    cz
    wcel
    cA
    cim
    cfv
    #
    cz
    wcel
    cA
    cgz
    wcel
    cA
    zcn
    @0
    @1
    cA
    cz
    @0
    cA
    cA
    zre
    #
    rered
    @0
    id
    eqeltrd
    @0
    @2
    cc0
    cz
    @0
    cA
    @3
    reim0d
    0z
    syl6eqel
    cA
    elgz
    syl3anbrc
end
