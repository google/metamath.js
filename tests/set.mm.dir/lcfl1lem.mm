include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "elrab2.mm"

theorem lcfl1lem
  let cC: class C
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cL: class L
  let c.pe: class ._|_
  assume lcfl1.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }

  disjoint F f
  disjoint G f
  disjoint L f
  disjoint ._|_ f
  assert |- ( G e. C <-> ( G e. F /\ ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) = ( L ` G ) ) )

  proof
    vf
    cv
    #
    cL
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @1
    wceq
    cG
    cL
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @4
    wceq
    vf
    cG
    cF
    cC
    @0
    cG
    wceq
    #
    @3
    @6
    @1
    @4
    @7
    @2
    @5
    c.pe
    @7
    @1
    @4
    c.pe
    @0
    cG
    cL
    fveq2
    #
    fveq2d
    fveq2d
    @8
    eqeq12d
    lcfl1.c
    elrab2
end
