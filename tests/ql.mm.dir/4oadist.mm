include "wo.mm"
include "wa.mm"
include "wi1.mm"
include "le2or.mm"
include "oridm.mm"
include "lbtr.mm"
include "lelan.mm"
include "df2le2.mm"
include "ax-r1.mm"
include "or32.mm"
include "ax-r2.mm"
include "lan.mm"
include "leo.mm"
include "4oagen1b.mm"
include "lear.mm"
include "an32.mm"
include "lea.mm"
include "bltr.mm"
include "letr.mm"
include "leor.mm"
include "ledi.mm"
include "lebi.mm"

theorem 4oadist
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  param wve: term e
  param wvf: term f
  param wvh: term h
  param wvj: term j
  param wvk: term k
  assume 4oa.1: |- e = ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) )
  assume 4oa.2: |- f = ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v e )
  assume 4oadist.1: |- h =< ( a ->1 d )
  assume 4oadist.2: |- j =< f
  assume 4oadist.3: |- k =< f
  assume 4oadist.4: |- ( h ^ ( b ->1 d ) ) =< k


  assert |- ( h ^ ( j v k ) ) = ( ( h ^ j ) v ( h ^ k ) )

  proof
    wvh
    wvj
    wvk
    wo
    #
    wa
    #
    wvh
    wvj
    wa
    #
    wvh
    wvk
    wa
    #
    wo
    #
    @1
    @3
    @4
    @1
    @1
    wvh
    wvb
    wvd
    wi1
    #
    wa
    #
    wa
    #
    @3
    @1
    @1
    wvh
    wvf
    wa
    #
    wa
    #
    @7
    @9
    @1
    @1
    @8
    @0
    wvf
    wvh
    @0
    wvf
    wvf
    wo
    wvf
    wvj
    wvf
    wvk
    wvf
    4oadist.2
    4oadist.3
    le2or
    wvf
    oridm
    lbtr
    lelan
    df2le2
    ax-r1
    @8
    @6
    @1
    @8
    wvh
    wva
    wvb
    wa
    #
    wve
    wo
    #
    wva
    wvd
    wi1
    @5
    wa
    #
    wo
    #
    wa
    @6
    wvf
    @13
    wvh
    wvf
    @10
    @12
    wo
    wve
    wo
    @13
    4oa.2
    @10
    @12
    wve
    or32
    ax-r2
    #
    lan
    wva
    wvb
    wvc
    wvd
    wve
    wvf
    @11
    wvh
    4oa.1
    4oa.2
    @11
    @13
    wvf
    @11
    @12
    leo
    wvf
    @13
    @14
    ax-r1
    lbtr
    4oadist.1
    4oagen1b
    ax-r2
    lan
    ax-r2
    @7
    @6
    @3
    @1
    @6
    lear
    @6
    @3
    @5
    wa
    #
    @3
    @6
    @6
    wvk
    wa
    #
    @15
    @16
    @6
    @6
    wvk
    4oadist.4
    df2le2
    ax-r1
    wvh
    @5
    wvk
    an32
    ax-r2
    @3
    @5
    lea
    bltr
    letr
    bltr
    @3
    @2
    leor
    letr
    wvh
    wvj
    wvk
    ledi
    lebi
end
