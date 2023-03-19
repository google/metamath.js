include "wcel.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "c2.mm"
include "cabs.mm"
include "cfv.mm"
include "clogb.mm"
include "co.mm"
include "cfl.mm"
include "caddc.mm"
include "cif.mm"
include "cvv.mm"
include "cblen.mm"
include "cmpt.mm"
include "df-blen.mm"
include "a1i.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "ifbieq2d.mm"
include "adantl.mm"
include "elex.mm"
include "1ex.mm"
include "ovex.mm"
include "ifex.mm"
include "fvmptd.mm"

theorem blenval
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. V -> ( #b ` N ) = if ( N = 0 , 1 , ( ( |_ ` ( 2 logb ( abs ` N ) ) ) + 1 ) ) )

  proof
    cN
    cV
    wcel
    #
    vn
    cN
    vn
    cv
    #
    cc0
    wceq
    #
    c1
    c2
    @1
    cabs
    cfv
    #
    clogb
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cif
    #
    cN
    cc0
    wceq
    #
    c1
    c2
    cN
    cabs
    cfv
    #
    clogb
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cif
    #
    cvv
    cblen
    cvv
    cblen
    vn
    cvv
    @7
    cmpt
    wceq
    @0
    vn
    df-blen
    a1i
    @1
    cN
    wceq
    #
    @7
    @13
    wceq
    @0
    @14
    @2
    @8
    @6
    @12
    c1
    @1
    cN
    cc0
    eqeq1
    @14
    @5
    @11
    c1
    caddc
    @14
    @4
    @10
    cfl
    @14
    @3
    @9
    c2
    clogb
    @1
    cN
    cabs
    fveq2
    oveq2d
    fveq2d
    oveq1d
    ifbieq2d
    adantl
    cN
    cV
    elex
    @13
    cvv
    wcel
    @0
    @8
    c1
    @12
    1ex
    @11
    c1
    caddc
    ovex
    ifex
    a1i
    fvmptd
end
