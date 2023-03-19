include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cn0.mm"
include "zsqcl.mm"
include "cr.mm"
include "zre.mm"
include "sqge0.mm"
include "syl.mm"
include "elnn0z.mm"
include "sylanbrc.mm"

theorem zsqcl2
  let cA: class A


  assert |- ( A e. ZZ -> ( A ^ 2 ) e. NN0 )

  proof
    cA
    cz
    wcel
    #
    cA
    c2
    cexp
    co
    #
    cz
    wcel
    cc0
    @1
    cle
    wbr
    #
    @1
    cn0
    wcel
    cA
    zsqcl
    @0
    cA
    cr
    wcel
    @2
    cA
    zre
    cA
    sqge0
    syl
    @1
    elnn0z
    sylanbrc
end
