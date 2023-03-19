include "cmnc.mm"
include "cfv.mm"
include "wcel.mm"
include "cply.mm"
include "cdgr.mm"
include "ccoe.mm"
include "c1.mm"
include "wceq.mm"
include "elmnc.mm"
include "simplbi.mm"

theorem mncply
  let cP: class P
  let cS: class S
  let vs: setvar s
  let vp: setvar p


  assert |- ( P e. ( Monic ` S ) -> P e. ( Poly ` S ) )

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
    simplbi
end
