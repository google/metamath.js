include "crusgr.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cusgr.mm"
include "cfusgr.mm"
include "rusgrusgr.mm"
include "anim1i.mm"
include "isfusgr.mm"
include "sylibr.mm"

theorem finrusgrfusgr
  let cG: class G
  let cK: class K
  let cV: class V
  assume finrusgrfusgr.v: |- V = ( Vtx ` G )


  assert |- ( ( G RegUSGraph K /\ V e. Fin ) -> G e. FinUSGraph )

  proof
    cG
    cK
    crusgr
    wbr
    #
    cV
    cfn
    wcel
    #
    wa
    cG
    cusgr
    wcel
    #
    @1
    wa
    cG
    cfusgr
    wcel
    @0
    @2
    @1
    cG
    cK
    rusgrusgr
    anim1i
    cG
    cV
    finrusgrfusgr.v
    isfusgr
    sylibr
end
