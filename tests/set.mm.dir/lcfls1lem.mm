include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "elrab2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem lcfls1lem
  let cC: class C
  let cQ: class Q
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cL: class L
  let c.pe: class ._|_
  assume lcfls1.c: |- C = { f e. F | ( ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) /\ ( ._|_ ` ( L ` f ) ) C_ Q ) }

  disjoint F f
  disjoint G f
  disjoint L f
  disjoint ._|_ f
  disjoint Q f
  assert |- ( G e. C <-> ( G e. F /\ ( ._|_ ` ( ._|_ ` ( L ` G ) ) ) = ( L ` G ) /\ ( ._|_ ` ( L ` G ) ) C_ Q ) )

  proof
    cG
    cC
    wcel
    cG
    cF
    wcel
    #
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
    @1
    wceq
    #
    @2
    cQ
    wss
    #
    wa
    #
    wa
    @0
    @4
    @5
    w3a
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
    @8
    wceq
    #
    @9
    cQ
    wss
    #
    wa
    @6
    vf
    cG
    cF
    cC
    @7
    cG
    wceq
    #
    @11
    @4
    @12
    @5
    @13
    @10
    @3
    @8
    @1
    @13
    @9
    @2
    c.pe
    @13
    @8
    @1
    c.pe
    @7
    cG
    cL
    fveq2
    #
    fveq2d
    #
    fveq2d
    @14
    eqeq12d
    @13
    @9
    @2
    cQ
    @15
    sseq1d
    anbi12d
    lcfls1.c
    elrab2
    @0
    @4
    @5
    3anass
    bitr4i
end
