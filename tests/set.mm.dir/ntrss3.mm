include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "cnt.mm"
include "cfv.mm"
include "ntropn.mm"
include "eltopss.mm"
include "syldan.mm"

theorem ntrss3
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


  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( int ` J ) ` S ) C_ X )

  proof
    cJ
    ctop
    wcel
    cS
    cX
    wss
    cS
    cJ
    cnt
    cfv
    cfv
    #
    cJ
    wcel
    @0
    cX
    wss
    cS
    cJ
    cX
    clscld.1
    ntropn
    @0
    cJ
    cX
    clscld.1
    eltopss
    syldan
end
