include "cv.mm"
include "csetrecs.mm"
include "wss.mm"
include "wcel.mm"
include "wi.mm"
include "cvv.mm"
include "wceq.mm"
include "setind.mm"
include "cpw.mm"
include "vex.mm"
include "pwid.mm"
include "cfv.mm"
include "pweq.mm"
include "pwex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "eqid.mm"
include "a1i.mm"
include "id.mm"
include "setrec1.mm"
include "syl5eqssr.mm"
include "sseld.mm"
include "mpi.mm"
include "mpg.mm"

theorem vsetrec
  let vx: setvar x
  let cF: class F
  let va: setvar a
  let vk: setvar k
  assume vsetrec.1: |- F = ( x e. _V |-> ~P x )


  assert |- setrecs ( F ) = _V

  proof
    va
    cv
    #
    cF
    csetrecs
    #
    wss
    #
    @0
    @1
    wcel
    #
    wi
    @1
    cvv
    wceq
    va
    va
    @1
    setind
    @2
    @0
    @0
    cpw
    #
    wcel
    @3
    @0
    va
    vex
    #
    pwid
    @2
    @4
    @1
    @0
    @2
    @4
    @0
    cF
    cfv
    #
    @1
    @0
    cvv
    wcel
    #
    @6
    @4
    wceq
    @5
    vx
    @0
    vx
    cv
    #
    cpw
    @4
    cvv
    cF
    @8
    @0
    pweq
    vsetrec.1
    @0
    @5
    pwex
    fvmpt
    ax-mp
    @2
    @0
    @1
    cF
    @1
    eqid
    @7
    @2
    @5
    a1i
    @2
    id
    setrec1
    syl5eqssr
    sseld
    mpi
    mpg
end
