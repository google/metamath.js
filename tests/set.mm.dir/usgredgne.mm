include "cusgr.mm"
include "wcel.mm"
include "cumgr.mm"
include "cpr.mm"
include "wne.mm"
include "usgrumgr.mm"
include "umgredgne.mm"
include "sylan.mm"

theorem usgredgne
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  assume usgredgne.v: |- E = ( Edg ` G )


  assert |- ( ( G e. USGraph /\ { M , N } e. E ) -> M =/= N )

  proof
    cG
    cusgr
    wcel
    cG
    cumgr
    wcel
    cM
    cN
    cpr
    cE
    wcel
    cM
    cN
    wne
    cG
    usgrumgr
    cE
    cG
    cM
    cN
    usgredgne.v
    umgredgne
    sylan
end
