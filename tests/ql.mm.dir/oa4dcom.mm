include "wa.mm"
include "wi1.mm"
include "wo.mm"
include "ancom.mm"
include "2or.mm"
include "lan.mm"

theorem oa4dcom
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d


  assert |- ( b ^ ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) = ( b ^ ( ( ( b ^ a ) v ( ( b ->1 d ) ^ ( a ->1 d ) ) ) v ( ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ) ) )

  proof
    wva
    wvb
    wa
    #
    wva
    wvd
    wi1
    #
    wvb
    wvd
    wi1
    #
    wa
    #
    wo
    #
    wva
    wvc
    wa
    @1
    wvc
    wvd
    wi1
    #
    wa
    wo
    #
    wvb
    wvc
    wa
    @2
    @5
    wa
    wo
    #
    wa
    #
    wo
    wvb
    wva
    wa
    #
    @2
    @1
    wa
    #
    wo
    #
    @7
    @6
    wa
    #
    wo
    wvb
    @4
    @11
    @8
    @12
    @0
    @9
    @3
    @10
    wva
    wvb
    ancom
    @1
    @2
    ancom
    2or
    @6
    @7
    ancom
    2or
    lan
end
