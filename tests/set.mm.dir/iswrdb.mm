include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "wrdf.mm"
include "iswrdi.mm"
include "impbii.mm"

theorem iswrdb
  let cS: class S
  let cW: class W


  assert |- ( W e. Word S <-> W : ( 0 ..^ ( # ` W ) ) --> S )

  proof
    cW
    cS
    cword
    wcel
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    cS
    cW
    wf
    cS
    cW
    wrdf
    cS
    @0
    cW
    iswrdi
    impbii
end
