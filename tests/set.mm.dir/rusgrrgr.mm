include "crusgr.mm"
include "wbr.mm"
include "cusgr.mm"
include "wcel.mm"
include "crgr.mm"
include "rusgrprop.mm"
include "simprd.mm"

theorem rusgrrgr
  let cG: class G
  let cK: class K


  assert |- ( G RegUSGraph K -> G RegGraph K )

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
    simprd
end
