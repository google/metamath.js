include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wfn.mm"
include "cdm.mm"
include "wceq.mm"
include "wnel.mm"
include "wrdfn.mm"
include "fndm.mm"
include "fzonel.mm"
include "nelir.mm"
include "neleq2.mm"
include "mpbiri.mm"
include "3syl.mm"

theorem wrdlndm
  let cV: class V
  let cW: class W


  assert |- ( W e. Word V -> ( # ` W ) e/ dom W )

  proof
    cW
    cV
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
    cW
    cdm
    #
    @1
    wceq
    #
    @0
    @2
    wnel
    #
    cV
    cW
    wrdfn
    @1
    cW
    fndm
    @3
    @4
    @0
    @1
    wnel
    @0
    @1
    cc0
    @0
    fzonel
    nelir
    @2
    @1
    @0
    neleq2
    mpbiri
    3syl
end
