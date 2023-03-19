include "cn0.mm"
include "wcel.mm"
include "cfmtno.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "fmtno.mm"
include "oveq1d.mm"
include "cc.mm"
include "wceq.mm"
include "2nn0.mm"
include "a1i.mm"
include "id.mm"
include "nn0expcld.mm"
include "nn0cnd.mm"
include "pncan1.mm"
include "syl.mm"
include "eqtrd.mm"

theorem fmtnom1nn
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN0 -> ( ( FermatNo ` N ) - 1 ) = ( 2 ^ ( 2 ^ N ) ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    cfmtno
    cfv
    #
    c1
    cmin
    co
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
    c1
    cmin
    co
    #
    @3
    @0
    @1
    @4
    c1
    cmin
    cN
    fmtno
    oveq1d
    @0
    @3
    cc
    wcel
    @5
    @3
    wceq
    @0
    @3
    @0
    c2
    @2
    c2
    cn0
    wcel
    @0
    2nn0
    a1i
    #
    @0
    c2
    cN
    @6
    @0
    id
    nn0expcld
    nn0expcld
    nn0cnd
    @3
    pncan1
    syl
    eqtrd
end
