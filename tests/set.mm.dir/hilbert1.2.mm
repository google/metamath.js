include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "clines2.mm"
include "wral.mm"
include "wrmo.mm"
include "an4.mm"
include "cline2.mm"
include "co.mm"
include "wceq.mm"
include "simprl.mm"
include "simprr.mm"
include "simpl.mm"
include "linethru.mm"
include "syl3anc.mm"
include "ex.mm"
include "anim12d.mm"
include "eqtr3.mm"
include "syl6.mm"
include "syl5bi.mm"
include "expd.mm"
include "ralrimivv.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "rmo4.mm"
include "sylibr.mm"

theorem hilbert1.2
  let vx: setvar x
  let cP: class P
  let cQ: class Q
  let vy: setvar y

  disjoint P x
  disjoint Q x
  disjoint P y
  disjoint Q y
  disjoint x y
  assert |- ( P =/= Q -> E* x e. LinesEE ( P e. x /\ Q e. x ) )

  proof
    cP
    cQ
    wne
    #
    cP
    vx
    cv
    #
    wcel
    #
    cQ
    @1
    wcel
    #
    wa
    #
    cP
    vy
    cv
    #
    wcel
    #
    cQ
    @5
    wcel
    #
    wa
    #
    wa
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    clines2
    wral
    vx
    clines2
    wral
    @4
    vx
    clines2
    wrmo
    @0
    @11
    vx
    vy
    clines2
    clines2
    @0
    @1
    clines2
    wcel
    #
    @5
    clines2
    wcel
    #
    wa
    #
    @9
    @10
    @14
    @9
    wa
    @12
    @4
    wa
    #
    @13
    @8
    wa
    #
    wa
    #
    @0
    @10
    @12
    @13
    @4
    @8
    an4
    @0
    @17
    @1
    cP
    cQ
    cline2
    co
    #
    wceq
    #
    @5
    @18
    wceq
    #
    wa
    @10
    @0
    @15
    @19
    @16
    @20
    @0
    @15
    @19
    @0
    @15
    wa
    @12
    @4
    @0
    @19
    @0
    @12
    @4
    simprl
    @0
    @12
    @4
    simprr
    @0
    @15
    simpl
    @1
    cP
    cQ
    linethru
    syl3anc
    ex
    @0
    @16
    @20
    @0
    @16
    wa
    @13
    @8
    @0
    @20
    @0
    @13
    @8
    simprl
    @0
    @13
    @8
    simprr
    @0
    @16
    simpl
    @5
    cP
    cQ
    linethru
    syl3anc
    ex
    anim12d
    @1
    @5
    @18
    eqtr3
    syl6
    syl5bi
    expd
    ralrimivv
    @4
    @8
    vx
    vy
    clines2
    @10
    @2
    @6
    @3
    @7
    @1
    @5
    cP
    eleq2
    @1
    @5
    cQ
    eleq2
    anbi12d
    rmo4
    sylibr
end
