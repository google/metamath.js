include "wi1.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "oa4to4u.mm"
include "u1lem8.mm"
include "lear.mm"
include "lel2or.mm"
include "bltr.mm"
include "letr.mm"

theorem oa4to4u2
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  let wve: term e
  let wvf: term f
  let wvg: term g
  assume oa4to4u.1: |- ( ( e ->1 d ) ^ ( e v ( f ^ ( ( ( e ^ f ) v ( ( e ->1 d ) ^ ( f ->1 d ) ) ) v ( ( ( e ^ g ) v ( ( e ->1 d ) ^ ( g ->1 d ) ) ) ^ ( ( f ^ g ) v ( ( f ->1 d ) ^ ( g ->1 d ) ) ) ) ) ) ) ) =< ( ( ( e ^ d ) v ( f ^ d ) ) v ( g ^ d ) )
  assume oa4to4u.2: |- e = ( a ' ->1 d )
  assume oa4to4u3: |- f = ( b ' ->1 d )
  assume oa4to4u.4: |- g = ( c ' ->1 d )


  assert |- ( ( a ->1 d ) ^ ( ( a ' ->1 d ) v ( ( b ' ->1 d ) ^ ( ( ( ( a ->1 d ) ^ ( b ->1 d ) ) v ( ( a ' ->1 d ) ^ ( b ' ->1 d ) ) ) v ( ( ( ( a ->1 d ) ^ ( c ->1 d ) ) v ( ( a ' ->1 d ) ^ ( c ' ->1 d ) ) ) ^ ( ( ( b ->1 d ) ^ ( c ->1 d ) ) v ( ( b ' ->1 d ) ^ ( c ' ->1 d ) ) ) ) ) ) ) ) =< d

  proof
    wva
    wvd
    wi1
    #
    wva
    wn
    #
    wvd
    wi1
    #
    wvb
    wn
    #
    wvd
    wi1
    #
    @0
    wvb
    wvd
    wi1
    #
    wa
    @2
    @4
    wa
    wo
    @0
    wvc
    wvd
    wi1
    #
    wa
    @2
    wvc
    wn
    #
    wvd
    wi1
    #
    wa
    wo
    @5
    @6
    wa
    @4
    @8
    wa
    wo
    wa
    wo
    wa
    wo
    wa
    @0
    @2
    wa
    #
    @5
    @4
    wa
    #
    wo
    #
    @6
    @8
    wa
    #
    wo
    wvd
    wva
    wvb
    wvc
    wvd
    wve
    wvf
    wvg
    oa4to4u.1
    oa4to4u.2
    oa4to4u3
    oa4to4u.4
    oa4to4u
    @11
    wvd
    @12
    @9
    wvd
    @10
    @9
    wva
    wvd
    wa
    #
    @1
    wvd
    wa
    #
    wo
    wvd
    wva
    wvd
    u1lem8
    @13
    wvd
    @14
    wva
    wvd
    lear
    @1
    wvd
    lear
    lel2or
    bltr
    @10
    wvb
    wvd
    wa
    #
    @3
    wvd
    wa
    #
    wo
    wvd
    wvb
    wvd
    u1lem8
    @15
    wvd
    @16
    wvb
    wvd
    lear
    @3
    wvd
    lear
    lel2or
    bltr
    lel2or
    @12
    wvc
    wvd
    wa
    #
    @7
    wvd
    wa
    #
    wo
    wvd
    wvc
    wvd
    u1lem8
    @17
    wvd
    @18
    wvc
    wvd
    lear
    @7
    wvd
    lear
    lel2or
    bltr
    lel2or
    letr
end
