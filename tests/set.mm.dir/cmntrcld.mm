include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cnt.mm"
include "cfv.mm"
include "cdif.mm"
include "ccld.mm"
include "simpl.mm"
include "ntropn.mm"
include "opncld.mm"
include "syl2anc.mm"

theorem cmntrcld
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


  assert |- ( ( J e. Top /\ S C_ X ) -> ( X \ ( ( int ` J ) ` S ) ) e. ( Clsd ` J ) )

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
    @0
    cS
    cJ
    cnt
    cfv
    cfv
    #
    cJ
    wcel
    cX
    @2
    cdif
    cJ
    ccld
    cfv
    wcel
    @0
    @1
    simpl
    cS
    cJ
    cX
    clscld.1
    ntropn
    @2
    cJ
    cX
    clscld.1
    opncld
    syl2anc
end
