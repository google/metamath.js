include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "cfv.mm"
include "wss.mm"
include "sgon.mm"
include "sigasspw.mm"
include "syl.mm"
include "sselda.mm"
include "elpwid.mm"

theorem elsigass
  let cA: class A
  let cS: class S


  assert |- ( ( S e. U. ran sigAlgebra /\ A e. S ) -> A C_ U. S )

  proof
    cS
    csiga
    crn
    cuni
    wcel
    #
    cA
    cS
    wcel
    wa
    cA
    cS
    cuni
    #
    @0
    cS
    @1
    cpw
    #
    cA
    @0
    cS
    @1
    csiga
    cfv
    wcel
    cS
    @2
    wss
    cS
    sgon
    @1
    cS
    sigasspw
    syl
    sselda
    elpwid
end
