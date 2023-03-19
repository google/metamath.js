include "wi1.mm"
include "wa.mm"
include "wo.mm"
include "4oaiii.mm"
include "lan.mm"
include "or32.mm"
include "ax-r2.mm"
include "2an.mm"
include "anidm.mm"
include "ax-r1.mm"
include "anandir.mm"
include "3tr1.mm"
include "ax-a2.mm"
include "anabs.mm"
include "3tr.mm"

theorem 4oath1
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  let wve: term e
  let wvf: term f
  assume 4oa.1: |- e = ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) )
  assume 4oa.2: |- f = ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v e )


  assert |- ( ( a ->1 d ) ^ f ) = ( ( a ->1 d ) ^ ( b ->1 d ) )

  proof
    wva
    wvd
    wi1
    #
    wvf
    wa
    #
    @0
    wvb
    wvd
    wi1
    #
    wa
    #
    wva
    wvb
    wa
    #
    wve
    wo
    #
    @3
    wo
    #
    wa
    #
    @3
    @3
    @5
    wo
    #
    wa
    @3
    @1
    @1
    wa
    #
    @0
    @6
    wa
    #
    @2
    @6
    wa
    #
    wa
    #
    @1
    @7
    @9
    @1
    @2
    wvf
    wa
    #
    wa
    @12
    @1
    @13
    @1
    wva
    wvb
    wvc
    wvd
    wve
    wvf
    4oa.1
    4oa.2
    4oaiii
    lan
    @1
    @10
    @13
    @11
    wvf
    @6
    @0
    wvf
    @4
    @3
    wo
    wve
    wo
    @6
    4oa.2
    @4
    @3
    wve
    or32
    ax-r2
    #
    lan
    wvf
    @6
    @2
    @14
    lan
    2an
    ax-r2
    @9
    @1
    @1
    anidm
    ax-r1
    @0
    @2
    @6
    anandir
    3tr1
    @6
    @8
    @3
    @5
    @3
    ax-a2
    lan
    @3
    @5
    anabs
    3tr
end
