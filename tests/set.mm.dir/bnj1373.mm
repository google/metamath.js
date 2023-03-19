include "cv.mm"
include "wsbc.mm"
include "wcel.mm"
include "cdm.mm"
include "csn.mm"
include "c-bnj18.mm"
include "cun.mm"
include "wceq.mm"
include "wa.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "bnj1309.mm"
include "bnj1307.mm"
include "bnj1351.mm"
include "nf5i.mm"
include "weq.mm"
include "sneq.mm"
include "bnj1318.mm"
include "uneq12d.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "sbciegf.mm"
include "ax-mp.mm"
include "bitri.mm"

theorem bnj1373
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  let cG: class G
  let cY: class Y
  let vd: setvar d
  let bnjwtam: wff ta'
  assume bnj1373.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1373.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1373.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1373.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1373.5: |- ( ta' <-> [. y / x ]. ta )

  disjoint A x
  disjoint B f
  disjoint R x
  disjoint d f
  disjoint d x
  disjoint f x
  disjoint x y
  assert |- ( ta' <-> ( f e. C /\ dom f = ( { y } u. _trCl ( y , A , R ) ) ) )

  proof
    bnjwtam
    wta
    vx
    vy
    cv
    #
    wsbc
    #
    vf
    cv
    #
    cC
    wcel
    #
    @2
    cdm
    #
    @0
    csn
    #
    cA
    cR
    @0
    c-bnj18
    #
    cun
    #
    wceq
    #
    wa
    #
    bnj1373.5
    @0
    cvv
    wcel
    @1
    @9
    wb
    vy
    vex
    wta
    @9
    vx
    @0
    cvv
    @9
    vx
    @3
    @8
    vx
    vx
    vf
    cB
    cC
    vf
    cG
    cY
    vd
    bnj1373.3
    vx
    vf
    cA
    cB
    cR
    vd
    bnj1373.1
    bnj1309
    bnj1307
    bnj1351
    nf5i
    wta
    @3
    @4
    vx
    cv
    #
    csn
    #
    cA
    cR
    @10
    c-bnj18
    #
    cun
    #
    wceq
    #
    wa
    vx
    vy
    weq
    #
    @9
    bnj1373.4
    @15
    @14
    @8
    @3
    @15
    @13
    @7
    @4
    @15
    @11
    @5
    @12
    @6
    @10
    @0
    sneq
    cA
    cR
    @10
    @0
    bnj1318
    uneq12d
    eqeq2d
    anbi2d
    syl5bb
    sbciegf
    ax-mp
    bitri
end
