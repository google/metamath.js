include "cz.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "wceq.mm"
include "cn.mm"
include "cneg.mm"
include "w3o.mm"
include "wa.mm"
include "elz.mm"
include "negeq.mm"
include "neg0.mm"
include "syl6eq.mm"
include "0z.mm"
include "syl6eqel.mm"
include "nnnegz.mm"
include "nnz.mm"
include "3jaoi.mm"
include "adantl.mm"
include "sylbi.mm"

theorem znegcl
  let cN: class N


  assert |- ( N e. ZZ -> -u N e. ZZ )

  proof
    cN
    cz
    wcel
    cN
    cr
    wcel
    #
    cN
    cc0
    wceq
    #
    cN
    cn
    wcel
    #
    cN
    cneg
    #
    cn
    wcel
    #
    w3o
    #
    wa
    @3
    cz
    wcel
    #
    cN
    elz
    @5
    @6
    @0
    @1
    @6
    @2
    @4
    @1
    @3
    cc0
    cz
    @1
    @3
    cc0
    cneg
    cc0
    cN
    cc0
    negeq
    neg0
    syl6eq
    0z
    syl6eqel
    cN
    nnnegz
    @3
    nnz
    3jaoi
    adantl
    sylbi
end
