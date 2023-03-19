include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cnt.mm"
include "cfv.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "ntrval.mm"
include "inss2.mm"
include "unissi.mm"
include "unipw.mm"
include "sseqtri.mm"
include "syl6eqss.mm"

theorem ntrss2
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


  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( int ` J ) ` S ) C_ S )

  proof
    cJ
    ctop
    wcel
    cS
    cX
    wss
    wa
    cS
    cJ
    cnt
    cfv
    cfv
    cJ
    cS
    cpw
    #
    cin
    #
    cuni
    #
    cS
    cS
    cJ
    cX
    clscld.1
    ntrval
    @2
    @0
    cuni
    cS
    @1
    @0
    cJ
    @0
    inss2
    unissi
    cS
    unipw
    sseqtri
    syl6eqss
end
