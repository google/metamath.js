include "crecs.mm"
include "wfun.mm"
include "wrel.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "tfrlem6.mm"
include "wex.mm"
include "cuni.mm"
include "recsfval.mm"
include "eleq2i.mm"
include "eluni.mm"
include "bitri.mm"
include "anbi12i.mm"
include "eeanv.mm"
include "bitr4i.mm"
include "wbr.mm"
include "df-br.mm"
include "tfrlem5.mm"
include "impcom.mm"
include "sylanbr.mm"
include "an4s.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "ax-gen.mm"
include "gen2.mm"
include "dffun4.mm"
include "mpbir2an.mm"

theorem tfrlem7
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let cF: class F
  let vg: setvar g
  let vz: setvar z
  let cB: class B
  let cC: class C
  let va: setvar a
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume tfrlem.1: |- A = { f | E. x e. On ( f Fn x /\ A. y e. x ( f ` y ) = ( F ` ( f |` y ) ) ) }

  disjoint f x
  disjoint f y
  disjoint x y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint f g
  disjoint f z
  disjoint B f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint f h
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint g h
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint F g
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint F h
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint A g
  disjoint A h
  disjoint A z
  assert |- Fun recs ( F )

  proof
    cF
    crecs
    #
    wfun
    @0
    wrel
    vx
    cv
    #
    vu
    cv
    #
    cop
    #
    @0
    wcel
    #
    @1
    vv
    cv
    #
    cop
    #
    @0
    wcel
    #
    wa
    #
    @2
    @5
    wceq
    #
    wi
    #
    vv
    wal
    #
    vu
    wal
    vx
    wal
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    tfrlem6
    @11
    vx
    vu
    @10
    vv
    @8
    @3
    vg
    cv
    #
    wcel
    #
    @12
    cA
    wcel
    #
    wa
    #
    @6
    vh
    cv
    #
    wcel
    #
    @16
    cA
    wcel
    #
    wa
    #
    wa
    #
    vh
    wex
    vg
    wex
    #
    @9
    @8
    @15
    vg
    wex
    #
    @19
    vh
    wex
    #
    wa
    @21
    @4
    @22
    @7
    @23
    @4
    @3
    cA
    cuni
    #
    wcel
    @22
    @0
    @24
    @3
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    recsfval
    #
    eleq2i
    vg
    @3
    cA
    eluni
    bitri
    @7
    @6
    @24
    wcel
    @23
    @0
    @24
    @6
    @25
    eleq2i
    vh
    @6
    cA
    eluni
    bitri
    anbi12i
    @15
    @19
    vg
    vh
    eeanv
    bitr4i
    @20
    @9
    vg
    vh
    @13
    @17
    @14
    @18
    @9
    @13
    @17
    wa
    @1
    @2
    @12
    wbr
    #
    @1
    @5
    @16
    wbr
    #
    wa
    #
    @14
    @18
    wa
    #
    @9
    @26
    @13
    @27
    @17
    @1
    @2
    @12
    df-br
    @1
    @5
    @16
    df-br
    anbi12i
    @29
    @28
    @9
    vx
    vy
    vv
    vu
    cA
    vf
    vg
    vh
    cF
    tfrlem.1
    tfrlem5
    impcom
    sylanbr
    an4s
    exlimivv
    sylbi
    ax-gen
    gen2
    vx
    vu
    vv
    @0
    dffun4
    mpbir2an
end
