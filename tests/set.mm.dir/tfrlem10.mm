include "crecs.mm"
include "cdm.mm"
include "con0.mm"
include "wcel.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "csuc.mm"
include "wfn.mm"
include "wfun.mm"
include "wceq.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "cvv.mm"
include "fvex.mm"
include "funsng.mm"
include "mpan2.mm"
include "tfrlem7.mm"
include "jctil.mm"
include "dmsnop.mm"
include "ineq2i.mm"
include "word.mm"
include "tfrlem8.mm"
include "orddisj.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "funun.mm"
include "sylancl.mm"
include "uneq2i.mm"
include "dmun.mm"
include "df-suc.mm"
include "3eqtr4i.mm"
include "df-fn.mm"
include "sylanblrc.mm"
include "fneq1i.mm"
include "sylibr.mm"

theorem tfrlem10
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let vf: setvar f
  let cF: class F
  let vg: setvar g
  let vz: setvar z
  let cB: class B
  let va: setvar a
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume tfrlem.1: |- A = { f | E. x e. On ( f Fn x /\ A. y e. x ( f ` y ) = ( F ` ( f |` y ) ) ) }
  assume tfrlem.3: |- C = ( recs ( F ) u. { <. dom recs ( F ) , ( F ` recs ( F ) ) >. } )

  disjoint f x
  disjoint f y
  disjoint x y
  disjoint C f
  disjoint C x
  disjoint C y
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
  assert |- ( dom recs ( F ) e. On -> C Fn suc dom recs ( F ) )

  proof
    cF
    crecs
    #
    cdm
    #
    con0
    wcel
    #
    @0
    @1
    @0
    cF
    cfv
    #
    cop
    csn
    #
    cun
    #
    @1
    csuc
    #
    wfn
    #
    cC
    @6
    wfn
    @2
    @5
    wfun
    #
    @5
    cdm
    #
    @6
    wceq
    @7
    @2
    @0
    wfun
    #
    @4
    wfun
    #
    wa
    @1
    @4
    cdm
    #
    cin
    #
    c0
    wceq
    @8
    @2
    @11
    @10
    @2
    @3
    cvv
    wcel
    @11
    @0
    cF
    fvex
    #
    @1
    @3
    con0
    cvv
    funsng
    mpan2
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    tfrlem7
    jctil
    @13
    @1
    @1
    csn
    #
    cin
    #
    c0
    @12
    @15
    @1
    @1
    @3
    @14
    dmsnop
    #
    ineq2i
    @1
    word
    @16
    c0
    wceq
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    tfrlem8
    @1
    orddisj
    ax-mp
    eqtri
    @0
    @4
    funun
    sylancl
    @1
    @12
    cun
    @1
    @15
    cun
    @9
    @6
    @12
    @15
    @1
    @17
    uneq2i
    @0
    @4
    dmun
    @1
    df-suc
    3eqtr4i
    @5
    @6
    df-fn
    sylanblrc
    @6
    cC
    @5
    tfrlem.3
    fneq1i
    sylibr
end
