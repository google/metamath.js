include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cbc.mm"
include "co.mm"
include "cmin.mm"
include "cz.mm"
include "wceq.mm"
include "1z.mm"
include "bccmpl.mm"
include "mpan2.mm"
include "bcn1.mm"
include "eqtr3d.mm"

theorem bcnm1
  let cN: class N


  assert |- ( N e. NN0 -> ( N _C ( N - 1 ) ) = N )

  proof
    cN
    cn0
    wcel
    #
    cN
    c1
    cbc
    co
    #
    cN
    cN
    c1
    cmin
    co
    cbc
    co
    #
    cN
    @0
    c1
    cz
    wcel
    @1
    @2
    wceq
    1z
    c1
    cN
    bccmpl
    mpan2
    cN
    bcn1
    eqtr3d
end
