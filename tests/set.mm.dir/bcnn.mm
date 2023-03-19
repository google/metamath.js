include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cbc.mm"
include "co.mm"
include "cmin.mm"
include "c1.mm"
include "cz.mm"
include "wceq.mm"
include "0z.mm"
include "bccmpl.mm"
include "mpan2.mm"
include "bcn0.mm"
include "nn0cn.mm"
include "subid1d.mm"
include "oveq2d.mm"
include "3eqtr3rd.mm"

theorem bcnn
  let cN: class N


  assert |- ( N e. NN0 -> ( N _C N ) = 1 )

  proof
    cN
    cn0
    wcel
    #
    cN
    cc0
    cbc
    co
    #
    cN
    cN
    cc0
    cmin
    co
    #
    cbc
    co
    #
    c1
    cN
    cN
    cbc
    co
    @0
    cc0
    cz
    wcel
    @1
    @3
    wceq
    0z
    cc0
    cN
    bccmpl
    mpan2
    cN
    bcn0
    @0
    @2
    cN
    cN
    cbc
    @0
    cN
    cN
    nn0cn
    subid1d
    oveq2d
    3eqtr3rd
end
