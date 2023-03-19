include "crecs.mm"
include "cdm.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "csuc.mm"
include "con0.mm"
include "wrex.mm"
include "wlim.mm"
include "w3o.mm"
include "word.mm"
include "tfrlem8.mm"
include "ordzsl.mm"
include "mpbi.mm"
include "wcel.mm"
include "cres.mm"
include "cvv.mm"
include "res0.mm"
include "0ex.mm"
include "eqeltri.mm"
include "wb.mm"
include "0elon.mm"
include "tfrlem15.mm"
include "ax-mp.mm"
include "mpbir.mm"
include "n0ii.mm"
include "pm2.21i.mm"
include "tfrlem13.mm"
include "wa.mm"
include "csn.mm"
include "cun.mm"
include "simpr.mm"
include "df-suc.mm"
include "syl6eq.mm"
include "reseq2d.mm"
include "wrel.mm"
include "tfrlem6.mm"
include "resdm.mm"
include "resundi.mm"
include "3eqtr3g.mm"
include "vex.mm"
include "sucid.mm"
include "syl5eleqr.mm"
include "tfrlem9a.mm"
include "syl.mm"
include "cfv.mm"
include "cop.mm"
include "snex.mm"
include "wfun.mm"
include "wss.mm"
include "tfrlem7.mm"
include "funressn.mm"
include "ssexi.mm"
include "unexg.mm"
include "sylancl.mm"
include "eqeltrd.mm"
include "rexlimiva.mm"
include "mto.mm"
include "id.mm"
include "3jaoi.mm"

theorem tfrlem16
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
  assert |- Lim dom recs ( F )

  proof
    cF
    crecs
    #
    cdm
    #
    c0
    wceq
    #
    @1
    vz
    cv
    #
    csuc
    #
    wceq
    #
    vz
    con0
    wrex
    #
    @1
    wlim
    #
    w3o
    #
    @7
    @1
    word
    @8
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    tfrlem8
    vz
    @1
    ordzsl
    mpbi
    @2
    @7
    @6
    @7
    @2
    @7
    c0
    @1
    c0
    @1
    wcel
    #
    @0
    c0
    cres
    #
    cvv
    wcel
    #
    @10
    c0
    cvv
    @0
    res0
    0ex
    eqeltri
    c0
    con0
    wcel
    @9
    @11
    wb
    0elon
    vx
    vy
    cA
    c0
    vf
    cF
    tfrlem.1
    tfrlem15
    ax-mp
    mpbir
    n0ii
    pm2.21i
    @6
    @7
    @6
    @0
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
    @5
    @12
    vz
    con0
    @3
    con0
    wcel
    #
    @5
    wa
    #
    @0
    @0
    @3
    cres
    #
    @0
    @3
    csn
    #
    cres
    #
    cun
    #
    cvv
    @14
    @0
    @1
    cres
    #
    @0
    @3
    @16
    cun
    #
    cres
    @0
    @18
    @14
    @1
    @20
    @0
    @14
    @1
    @4
    @20
    @13
    @5
    simpr
    #
    @3
    df-suc
    syl6eq
    reseq2d
    @0
    wrel
    @19
    @0
    wceq
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    tfrlem6
    @0
    resdm
    ax-mp
    @0
    @3
    @16
    resundi
    3eqtr3g
    @14
    @15
    cvv
    wcel
    #
    @17
    cvv
    wcel
    @18
    cvv
    wcel
    @14
    @3
    @1
    wcel
    @22
    @14
    @3
    @4
    @1
    @3
    vz
    vex
    sucid
    @21
    syl5eleqr
    vx
    vy
    cA
    @3
    vf
    cF
    tfrlem.1
    tfrlem9a
    syl
    @17
    @3
    @3
    @0
    cfv
    cop
    #
    csn
    #
    @23
    snex
    @0
    wfun
    @17
    @24
    wss
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    tfrlem7
    @3
    @0
    funressn
    ax-mp
    ssexi
    @15
    @17
    cvv
    cvv
    unexg
    sylancl
    eqeltrd
    rexlimiva
    mto
    pm2.21i
    @7
    id
    3jaoi
    ax-mp
end
