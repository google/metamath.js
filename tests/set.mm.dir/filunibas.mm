include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cuni.mm"
include "wss.mm"
include "wceq.mm"
include "cpw.mm"
include "filsspw.mm"
include "sspwuni.mm"
include "sylib.mm"
include "filtop.mm"
include "unissel.mm"
include "syl2anc.mm"

theorem filunibas
  let cF: class F
  let cX: class X
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x


  assert |- ( F e. ( Fil ` X ) -> U. F = X )

  proof
    cF
    cX
    cfil
    cfv
    wcel
    #
    cF
    cuni
    #
    cX
    wss
    #
    cX
    cF
    wcel
    @1
    cX
    wceq
    @0
    cF
    cX
    cpw
    wss
    @2
    cF
    cX
    filsspw
    cF
    cX
    sspwuni
    sylib
    cF
    cX
    filtop
    cF
    cX
    unissel
    syl2anc
end
