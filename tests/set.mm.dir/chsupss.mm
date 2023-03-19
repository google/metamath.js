include "cch.mm"
include "wss.mm"
include "chil.mm"
include "cpw.mm"
include "chsup.mm"
include "cfv.mm"
include "wi.mm"
include "chsspwh.mm"
include "sstr2.mm"
include "mpi.mm"
include "hsupss.mm"
include "syl2an.mm"

theorem chsupss
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A C_ CH /\ B C_ CH ) -> ( A C_ B -> ( \/H ` A ) C_ ( \/H ` B ) ) )

  proof
    cA
    cch
    wss
    #
    cA
    chil
    cpw
    #
    wss
    #
    cB
    @1
    wss
    #
    cA
    cB
    wss
    cA
    chsup
    cfv
    cB
    chsup
    cfv
    wss
    wi
    cB
    cch
    wss
    #
    @0
    cch
    @1
    wss
    #
    @2
    chsspwh
    cA
    cch
    @1
    sstr2
    mpi
    @4
    @5
    @3
    chsspwh
    cB
    cch
    @1
    sstr2
    mpi
    cA
    cB
    hsupss
    syl2an
end
