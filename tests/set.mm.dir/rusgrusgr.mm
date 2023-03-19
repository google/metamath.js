include "crusgr.mm"
include "wbr.mm"
include "cusgr.mm"
include "wcel.mm"
include "crgr.mm"
include "rusgrprop.mm"
include "simpld.mm"

theorem rusgrusgr
  let cG: class G
  let cK: class K


  assert |- ( G RegUSGraph K -> G e. USGraph )

  proof
    cG
    cK
    crusgr
    wbr
    cG
    cusgr
    wcel
    cG
    cK
    crgr
    wbr
    cG
    cK
    rusgrprop
    simpld
end
