include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "c1.mm"
include "cun.mm"
include "csn.mm"
include "wceq.mm"
include "0elfz.mm"
include "caddc.mm"
include "fzsplit.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "uneq2i.mm"
include "syl6eq.mm"
include "syl.mm"
include "cz.mm"
include "0z.mm"
include "fzsn.mm"
include "mp1i.mm"
include "uneq1d.mm"
include "eqtrd.mm"

theorem fz0sn0fz1
  let cN: class N


  assert |- ( N e. NN0 -> ( 0 ... N ) = ( { 0 } u. ( 1 ... N ) ) )

  proof
    cN
    cn0
    wcel
    #
    cc0
    cN
    cfz
    co
    #
    cc0
    cc0
    cfz
    co
    #
    c1
    cN
    cfz
    co
    #
    cun
    #
    cc0
    csn
    #
    @3
    cun
    @0
    cc0
    @1
    wcel
    #
    @1
    @4
    wceq
    cN
    0elfz
    @6
    @1
    @2
    cc0
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    cun
    @4
    cc0
    cc0
    cN
    fzsplit
    @8
    @3
    @2
    @7
    c1
    cN
    cfz
    0p1e1
    oveq1i
    uneq2i
    syl6eq
    syl
    @0
    @2
    @5
    @3
    cc0
    cz
    wcel
    @2
    @5
    wceq
    @0
    0z
    cc0
    fzsn
    mp1i
    uneq1d
    eqtrd
end
