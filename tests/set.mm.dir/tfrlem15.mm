include "con0.mm"
include "wcel.mm"
include "crecs.mm"
include "cdm.mm"
include "cres.mm"
include "cvv.mm"
include "tfrlem9a.mm"
include "adantl.mm"
include "wa.mm"
include "wss.mm"
include "wn.mm"
include "tfrlem13.mm"
include "simpr.mm"
include "resss.mm"
include "a1i.mm"
include "wrel.mm"
include "wceq.mm"
include "tfrlem6.mm"
include "resdm.mm"
include "ax-mp.mm"
include "ssres2.mm"
include "syl5eqssr.mm"
include "eqssd.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "mtoi.mm"
include "word.mm"
include "wb.mm"
include "tfrlem8.mm"
include "eloni.mm"
include "adantr.mm"
include "ordtri1.mm"
include "con2bid.mm"
include "sylancr.mm"
include "mpbird.mm"
include "impbida.mm"

theorem tfrlem15
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cF: class F
  let vg: setvar g
  let vz: setvar z
  let cC: class C
  let va: setvar a
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume tfrlem.1: |- A = { f | E. x e. On ( f Fn x /\ A. y e. x ( f ` y ) = ( F ` ( f |` y ) ) ) }

  disjoint f x
  disjoint f y
  disjoint B f
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint f g
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint x z
  disjoint y z
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
  assert |- ( B e. On -> ( B e. dom recs ( F ) <-> ( recs ( F ) |` B ) e. _V ) )

  proof
    cB
    con0
    wcel
    #
    cB
    cF
    crecs
    #
    cdm
    #
    wcel
    #
    @1
    cB
    cres
    #
    cvv
    wcel
    #
    @3
    @5
    @0
    vx
    vy
    cA
    cB
    vf
    cF
    tfrlem.1
    tfrlem9a
    adantl
    @0
    @5
    wa
    #
    @3
    @2
    cB
    wss
    #
    wn
    #
    @6
    @7
    @1
    cvv
    wcel
    #
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    tfrlem13
    @6
    @5
    @7
    @9
    @0
    @5
    simpr
    @7
    @4
    @1
    cvv
    @7
    @4
    @1
    @4
    @1
    wss
    @7
    @1
    cB
    resss
    a1i
    @7
    @1
    @1
    @2
    cres
    #
    @4
    @1
    wrel
    @10
    @1
    wceq
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    tfrlem6
    @1
    resdm
    ax-mp
    @2
    cB
    @1
    ssres2
    syl5eqssr
    eqssd
    eleq1d
    syl5ibcom
    mtoi
    @6
    @2
    word
    #
    cB
    word
    #
    @3
    @8
    wb
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    tfrlem8
    @0
    @12
    @5
    cB
    eloni
    adantr
    @11
    @12
    wa
    @7
    @3
    @2
    cB
    ordtri1
    con2bid
    sylancr
    mpbird
    impbida
end
