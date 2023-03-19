include "w-bnj15.mm"
include "cv.mm"
include "wcel.mm"
include "cdm.mm"
include "csn.mm"
include "c-bnj18.mm"
include "cun.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wn.mm"
include "crab.mm"
include "c0.mm"
include "wne.mm"
include "wbr.mm"
include "wral.mm"
include "w3a.mm"
include "wsbc.mm"
include "c-bnj14.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "cres.mm"
include "cop.mm"
include "cfv.mm"
include "biid.mm"
include "eqid.mm"
include "bnj1312.mm"

theorem bnj1493
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  let cG: class G
  let cY: class Y
  let vd: setvar d
  let vy: setvar y
  let vz: setvar z
  assume bnj1493.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1493.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1493.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }

  disjoint A d
  disjoint A f
  disjoint A x
  disjoint d f
  disjoint d x
  disjoint f x
  disjoint B f
  disjoint G d
  disjoint G f
  disjoint G x
  disjoint R d
  disjoint R f
  disjoint R x
  disjoint A y
  disjoint A z
  disjoint d y
  disjoint d z
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint G y
  disjoint G z
  disjoint R y
  disjoint R z
  disjoint Y z
  assert |- ( R _FrSe A -> A. x e. A E. f e. C dom f = ( { x } u. _trCl ( x , A , R ) ) )

  proof
    cA
    cR
    w-bnj15
    vf
    cv
    #
    cC
    wcel
    @0
    cdm
    vx
    cv
    #
    csn
    cA
    cR
    @1
    c-bnj18
    cun
    #
    wceq
    wa
    #
    vf
    wex
    wn
    vx
    cA
    crab
    #
    c0
    wne
    wa
    #
    @5
    @1
    @4
    wcel
    vy
    cv
    #
    @1
    cR
    wbr
    wn
    vy
    @4
    wral
    w3a
    #
    @3
    vx
    vy
    vz
    cA
    cB
    cC
    @4
    @3
    vx
    @6
    wsbc
    #
    vy
    cA
    cR
    @1
    c-bnj14
    #
    wrex
    vf
    cab
    #
    cuni
    #
    @11
    @1
    @1
    @11
    @9
    cres
    cop
    #
    cG
    cfv
    cop
    csn
    cun
    #
    cR
    vf
    @2
    cG
    @10
    vz
    cv
    #
    @13
    cA
    cR
    @14
    c-bnj14
    cres
    cop
    #
    cY
    @12
    vd
    @8
    bnj1493.1
    bnj1493.2
    bnj1493.3
    @3
    biid
    @4
    eqid
    @5
    biid
    @7
    biid
    @8
    biid
    @10
    eqid
    @11
    eqid
    @12
    eqid
    @13
    eqid
    @15
    eqid
    @2
    eqid
    bnj1312
end
