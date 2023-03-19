include "cgr.mm"
include "wcel.mm"
include "wa.mm"
include "cghomOLD.mm"
include "co.mm"
include "crn.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cab.mm"
include "eqid.mm"
include "elghomlem2OLD.mm"
include "feq23i.mm"
include "raleqi.mm"
include "raleqbii.mm"
include "anbi12i.mm"
include "syl6bbr.mm"

theorem elghomOLD
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cH: class H
  let cW: class W
  let cX: class X
  let vf: setvar f
  assume elghomOLD.1: |- X = ran G
  assume elghomOLD.2: |- W = ran H

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint X x
  disjoint X y
  disjoint F f
  disjoint f x
  disjoint f y
  disjoint G f
  disjoint H f
  assert |- ( ( G e. GrpOp /\ H e. GrpOp ) -> ( F e. ( G GrpOpHom H ) <-> ( F : X --> W /\ A. x e. X A. y e. X ( ( F ` x ) H ( F ` y ) ) = ( F ` ( x G y ) ) ) ) )

  proof
    cG
    cgr
    wcel
    cH
    cgr
    wcel
    wa
    cF
    cG
    cH
    cghomOLD
    co
    wcel
    cG
    crn
    #
    cH
    crn
    #
    cF
    wf
    #
    vx
    cv
    #
    cF
    cfv
    vy
    cv
    #
    cF
    cfv
    cH
    co
    @3
    @4
    cG
    co
    #
    cF
    cfv
    wceq
    #
    vy
    @0
    wral
    #
    vx
    @0
    wral
    #
    wa
    cX
    cW
    cF
    wf
    #
    @6
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    wa
    vx
    vy
    @0
    @1
    vf
    cv
    #
    wf
    @3
    @12
    cfv
    @4
    @12
    cfv
    cH
    co
    @5
    @12
    cfv
    wceq
    vy
    @0
    wral
    vx
    @0
    wral
    wa
    vf
    cab
    #
    vf
    cF
    cG
    cH
    @13
    eqid
    elghomlem2OLD
    @9
    @2
    @11
    @8
    cX
    cW
    @0
    @1
    cF
    elghomOLD.1
    elghomOLD.2
    feq23i
    @10
    @7
    vx
    cX
    @0
    elghomOLD.1
    @6
    vy
    cX
    @0
    elghomOLD.1
    raleqi
    raleqbii
    anbi12i
    syl6bbr
end
