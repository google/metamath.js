include "crn.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wral.mm"
include "crio.mm"
include "cmpt.mm"
include "eqid.mm"
include "wessf1ornlem.mm"

theorem wessf1orn
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cF: class F
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  assume wessf1orn.f: |- ( ph -> F Fn A )
  assume wessf1orn.a: |- ( ph -> A e. V )
  assume wessf1orn.r: |- ( ph -> R We A )

  disjoint A x
  disjoint F x
  disjoint R x
  disjoint F y
  disjoint F z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint R y
  disjoint R z
  assert |- ( ph -> E. x e. ~P A ( F |` x ) : x -1-1-onto-> ran F )

  proof
    wph
    vx
    vy
    vz
    cA
    cR
    cF
    vy
    cF
    crn
    vz
    cv
    vx
    cv
    cR
    wbr
    wn
    vz
    cF
    ccnv
    vy
    cv
    csn
    cima
    #
    wral
    vx
    @0
    crio
    cmpt
    #
    cV
    wessf1orn.f
    wessf1orn.a
    wessf1orn.r
    @1
    eqid
    wessf1ornlem
end
