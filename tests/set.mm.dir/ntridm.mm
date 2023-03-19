include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cnt.mm"
include "cfv.mm"
include "wceq.mm"
include "ntropn.mm"
include "wb.mm"
include "ntrss3.mm"
include "isopn3.mm"
include "syldan.mm"
include "mpbid.mm"

theorem ntridm
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cU: class U
  let cT: class T
  let cA: class A
  assume clscld.1: |- X = U. J


  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( int ` J ) ` ( ( int ` J ) ` S ) ) = ( ( int ` J ) ` S ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    wa
    cS
    cJ
    cnt
    cfv
    #
    cfv
    #
    cJ
    wcel
    #
    @3
    @2
    cfv
    @3
    wceq
    #
    cS
    cJ
    cX
    clscld.1
    ntropn
    @0
    @1
    @3
    cX
    wss
    @4
    @5
    wb
    cS
    cJ
    cX
    clscld.1
    ntrss3
    @3
    cJ
    cX
    clscld.1
    isopn3
    syldan
    mpbid
end
