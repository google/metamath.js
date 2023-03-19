include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cab.mm"
include "psubclsetN.mm"
include "eleq2d.mm"
include "cvv.mm"
include "catm.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssex.mm"
include "adantr.mm"
include "sseq1.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "elab3.mm"
include "syl6bb.mm"

theorem ispsubclN
  let cA: class A
  let cC: class C
  let cD: class D
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let vk: setvar k
  let vs: setvar s
  let vx: setvar x
  assume psubclset.a: |- A = ( Atoms ` K )
  assume psubclset.p: |- ._|_ = ( _|_P ` K )
  assume psubclset.c: |- C = ( PSubCl ` K )


  assert |- ( K e. D -> ( X e. C <-> ( X C_ A /\ ( ._|_ ` ( ._|_ ` X ) ) = X ) ) )

  proof
    cK
    cD
    wcel
    #
    cX
    cC
    wcel
    cX
    vx
    cv
    #
    cA
    wss
    #
    @1
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @1
    wceq
    #
    wa
    #
    vx
    cab
    #
    wcel
    cX
    cA
    wss
    #
    cX
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cX
    wceq
    #
    wa
    #
    @0
    cC
    @7
    cX
    cA
    cD
    cC
    cK
    c.pe
    vx
    psubclset.a
    psubclset.p
    psubclset.c
    psubclsetN
    eleq2d
    @6
    @12
    vx
    cX
    @8
    cX
    cvv
    wcel
    @11
    cX
    cA
    cA
    cK
    catm
    cfv
    cvv
    psubclset.a
    cK
    catm
    fvex
    eqeltri
    ssex
    adantr
    @1
    cX
    wceq
    #
    @2
    @8
    @5
    @11
    @1
    cX
    cA
    sseq1
    @13
    @4
    @10
    @1
    cX
    @13
    @3
    @9
    c.pe
    @1
    cX
    c.pe
    fveq2
    fveq2d
    @13
    id
    eqeq12d
    anbi12d
    elab3
    syl6bb
end
