include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cprime.mm"
include "cif.mm"
include "cprod.mm"
include "cprmo.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-prmo.mm"
include "a1i.mm"
include "oveq2.mm"
include "prodeq1d.mm"
include "adantl.mm"
include "id.mm"
include "prodex.mm"
include "fvmptd.mm"

theorem prmoval
  let vk: setvar k
  let cN: class N
  let vn: setvar n

  disjoint N k
  disjoint k n
  disjoint N n
  assert |- ( N e. NN0 -> ( #p ` N ) = prod_ k e. ( 1 ... N ) if ( k e. Prime , k , 1 ) )

  proof
    cN
    cn0
    wcel
    #
    vn
    cN
    c1
    vn
    cv
    #
    cfz
    co
    #
    vk
    cv
    #
    cprime
    wcel
    @3
    c1
    cif
    #
    vk
    cprod
    #
    c1
    cN
    cfz
    co
    #
    @4
    vk
    cprod
    #
    cn0
    cprmo
    cvv
    cprmo
    vn
    cn0
    @5
    cmpt
    wceq
    @0
    vk
    vn
    df-prmo
    a1i
    @1
    cN
    wceq
    #
    @5
    @7
    wceq
    @0
    @8
    @2
    @6
    @4
    vk
    @1
    cN
    c1
    cfz
    oveq2
    prodeq1d
    adantl
    @0
    id
    @7
    cvv
    wcel
    @0
    @6
    @4
    vk
    prodex
    a1i
    fvmptd
end
