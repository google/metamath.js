include "cmnc.mm"
include "cfv.mm"
include "wcel.mm"
include "cply.mm"
include "cdgr.mm"
include "ccoe.mm"
include "c1.mm"
include "wceq.mm"
include "elmnc.mm"
include "simprbi.mm"

theorem mnccoe
  let cP: class P
  let cS: class S
  let vs: setvar s
  let vp: setvar p


  assert |- ( P e. ( Monic ` S ) -> ( ( coeff ` P ) ` ( deg ` P ) ) = 1 )

  proof
    cP
    cS
    cmnc
    cfv
    wcel
    cP
    cS
    cply
    cfv
    wcel
    cP
    cdgr
    cfv
    cP
    ccoe
    cfv
    cfv
    c1
    wceq
    cP
    cS
    elmnc
    simprbi
end
