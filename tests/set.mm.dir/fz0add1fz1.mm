include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "cfz.mm"
include "cz.mm"
include "1z.mm"
include "fzoaddel.mm"
include "mpan2.mm"
include "adantl.mm"
include "wb.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "wceq.mm"
include "nn0z.mm"
include "fzval3.mm"
include "eqcomd.mm"
include "syl.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "adantr.mm"
include "mpbid.mm"

theorem fz0add1fz1
  let cN: class N
  let cX: class X


  assert |- ( ( N e. NN0 /\ X e. ( 0 ..^ N ) ) -> ( X + 1 ) e. ( 1 ... N ) )

  proof
    cN
    cn0
    wcel
    #
    cX
    cc0
    cN
    cfzo
    co
    wcel
    #
    wa
    cX
    c1
    caddc
    co
    #
    cc0
    c1
    caddc
    co
    #
    cN
    c1
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    @2
    c1
    cN
    cfz
    co
    #
    wcel
    #
    @1
    @6
    @0
    @1
    c1
    cz
    wcel
    @6
    1z
    cX
    cc0
    cN
    c1
    fzoaddel
    mpan2
    adantl
    @0
    @6
    @8
    wb
    @1
    @0
    @5
    @7
    @2
    @0
    @5
    c1
    @4
    cfzo
    co
    #
    @7
    @3
    c1
    @4
    cfzo
    0p1e1
    oveq1i
    @0
    cN
    cz
    wcel
    #
    @9
    @7
    wceq
    cN
    nn0z
    @10
    @7
    @9
    c1
    cN
    fzval3
    eqcomd
    syl
    syl5eq
    eleq2d
    adantr
    mpbid
end
