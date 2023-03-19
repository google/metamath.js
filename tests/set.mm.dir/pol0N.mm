include "wcel.mm"
include "c0.mm"
include "cfv.mm"
include "cv.mm"
include "coc.mm"
include "cpmap.mm"
include "ciin.mm"
include "cin.mm"
include "wss.mm"
include "wceq.mm"
include "0ss.mm"
include "eqid.mm"
include "polvalN.mm"
include "mpan2.mm"
include "cvv.mm"
include "0iin.mm"
include "ineq2i.mm"
include "inv1.mm"
include "eqtri.mm"
include "syl6eq.mm"

theorem pol0N
  let cA: class A
  let cB: class B
  let cK: class K
  let c.pe: class ._|_
  let vp: setvar p
  assume polssat.a: |- A = ( Atoms ` K )
  assume polssat.p: |- ._|_ = ( _|_P ` K )


  assert |- ( K e. B -> ( ._|_ ` (/) ) = A )

  proof
    cK
    cB
    wcel
    #
    c0
    c.pe
    cfv
    #
    cA
    vp
    c0
    vp
    cv
    cK
    coc
    cfv
    #
    cfv
    cK
    cpmap
    cfv
    #
    cfv
    #
    ciin
    #
    cin
    #
    cA
    @0
    c0
    cA
    wss
    @1
    @6
    wceq
    cA
    0ss
    cA
    cB
    c.pe
    cK
    @3
    @2
    c0
    vp
    @2
    eqid
    polssat.a
    @3
    eqid
    polssat.p
    polvalN
    mpan2
    @6
    cA
    cvv
    cin
    cA
    @5
    cvv
    cA
    vp
    @4
    0iin
    ineq2i
    cA
    inv1
    eqtri
    syl6eq
end
