include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cuz.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "csn.mm"
include "c1.mm"
include "cfzo.mm"
include "cun.mm"
include "wceq.mm"
include "elnn0uz.mm"
include "caddc.mm"
include "fzopredsuc.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "uneq2i.mm"
include "uneq1i.mm"
include "syl6eq.mm"
include "sylbi.mm"

theorem 1fzopredsuc
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN0 -> ( 0 ... N ) = ( ( { 0 } u. ( 1 ..^ N ) ) u. { N } ) )

  proof
    cN
    cn0
    wcel
    cN
    cc0
    cuz
    cfv
    wcel
    #
    cc0
    cN
    cfz
    co
    #
    cc0
    csn
    #
    c1
    cN
    cfzo
    co
    #
    cun
    #
    cN
    csn
    #
    cun
    #
    wceq
    cN
    elnn0uz
    @0
    @1
    @2
    cc0
    c1
    caddc
    co
    #
    cN
    cfzo
    co
    #
    cun
    #
    @5
    cun
    @6
    cc0
    cN
    fzopredsuc
    @9
    @4
    @5
    @8
    @3
    @2
    @7
    c1
    cN
    cfzo
    0p1e1
    oveq1i
    uneq2i
    uneq1i
    syl6eq
    sylbi
end
