include "crecs.mm"
include "cdm.mm"
include "word.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "con0.mm"
include "wss.mm"
include "wcel.mm"
include "wi.mm"
include "wfn.mm"
include "cfv.mm"
include "cres.mm"
include "wral.mm"
include "wa.mm"
include "tfrlem3.mm"
include "abeq2i.mm"
include "fndm.mm"
include "adantr.mm"
include "eleq1d.mm"
include "biimprcd.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "eleq1a.mm"
include "syl.mm"
include "abssi.mm"
include "ssorduni.mm"
include "ax-mp.mm"
include "wb.mm"
include "ciun.mm"
include "recsfval.mm"
include "dmeqi.mm"
include "dmuni.mm"
include "vex.mm"
include "dmex.mm"
include "dfiun2.mm"
include "3eqtri.mm"
include "ordeq.mm"
include "mpbir.mm"

theorem tfrlem8
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
  assert |- Ord dom recs ( F )

  proof
    cF
    crecs
    #
    cdm
    #
    word
    #
    vz
    cv
    #
    vg
    cv
    #
    cdm
    #
    wceq
    #
    vg
    cA
    wrex
    #
    vz
    cab
    #
    cuni
    #
    word
    #
    @8
    con0
    wss
    @10
    @7
    vz
    con0
    @6
    @3
    con0
    wcel
    #
    vg
    cA
    @4
    cA
    wcel
    #
    @5
    con0
    wcel
    #
    @6
    @11
    wi
    @12
    @4
    @3
    wfn
    #
    vw
    cv
    #
    @4
    cfv
    @4
    @15
    cres
    cF
    cfv
    wceq
    vw
    @3
    wral
    #
    wa
    #
    vz
    con0
    wrex
    #
    @13
    @18
    vg
    cA
    vx
    vy
    vz
    vw
    cA
    vf
    vg
    cF
    tfrlem.1
    tfrlem3
    abeq2i
    @17
    @13
    vz
    con0
    @17
    @13
    @11
    @17
    @5
    @3
    con0
    @14
    @5
    @3
    wceq
    @16
    @3
    @4
    fndm
    adantr
    eleq1d
    biimprcd
    rexlimiv
    sylbi
    @5
    con0
    @3
    eleq1a
    syl
    rexlimiv
    abssi
    @8
    ssorduni
    ax-mp
    @1
    @9
    wceq
    @2
    @10
    wb
    @1
    cA
    cuni
    #
    cdm
    vg
    cA
    @5
    ciun
    @9
    @0
    @19
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    recsfval
    dmeqi
    vg
    cA
    dmuni
    vg
    vz
    cA
    @5
    @4
    vg
    vex
    dmex
    dfiun2
    3eqtri
    @1
    @9
    ordeq
    ax-mp
    mpbir
end
