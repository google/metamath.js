include "cuhgr.mm"
include "wcel.mm"
include "cedg.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "ciedg.mm"
include "cc0.mm"
include "crgr.mm"
include "wbr.mm"
include "uhgriedg0edg0.mm"
include "biimpa.mm"
include "0edg0rgr.mm"
include "syldan.mm"

theorem uhgr0edg0rgr
  let cG: class G
  let vv: setvar v
  let cW: class W


  assert |- ( ( G e. UHGraph /\ ( Edg ` G ) = (/) ) -> G RegGraph 0 )

  proof
    cG
    cuhgr
    wcel
    #
    cG
    cedg
    cfv
    c0
    wceq
    #
    cG
    ciedg
    cfv
    c0
    wceq
    #
    cG
    cc0
    crgr
    wbr
    @0
    @1
    @2
    cG
    uhgriedg0edg0
    biimpa
    cG
    cuhgr
    0edg0rgr
    syldan
end
