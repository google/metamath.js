include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wfn.mm"
include "cfn.mm"
include "wrdfn.mm"
include "fzofi.mm"
include "fnfi.mm"
include "sylancl.mm"

theorem wrdfin
  let cS: class S
  let cW: class W


  assert |- ( W e. Word S -> W e. Fin )

  proof
    cW
    cS
    cword
    wcel
    cW
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    wfn
    @1
    cfn
    wcel
    cW
    cfn
    wcel
    cS
    cW
    wrdfn
    cc0
    @0
    fzofi
    @1
    cW
    fnfi
    sylancl
end
