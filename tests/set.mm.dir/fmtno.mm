include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cfmtno.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-fmtno.mm"
include "a1i.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "adantl.mm"
include "id.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem fmtno
  let cN: class N
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN0 -> ( FermatNo ` N ) = ( ( 2 ^ ( 2 ^ N ) ) + 1 ) )

  proof
    cN
    cn0
    wcel
    #
    vn
    cN
    c2
    c2
    vn
    cv
    #
    cexp
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    c2
    c2
    cN
    cexp
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    cn0
    cfmtno
    cvv
    cfmtno
    vn
    cn0
    @4
    cmpt
    wceq
    @0
    vn
    df-fmtno
    a1i
    @1
    cN
    wceq
    #
    @4
    @7
    wceq
    @0
    @8
    @3
    @6
    c1
    caddc
    @8
    @2
    @5
    c2
    cexp
    @1
    cN
    c2
    cexp
    oveq2
    oveq2d
    oveq1d
    adantl
    @0
    id
    @0
    @6
    c1
    caddc
    ovexd
    fvmptd
end
