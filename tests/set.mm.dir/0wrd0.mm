include "c0.mm"
include "cword.mm"
include "wcel.mm"
include "wceq.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "wrdf.mm"
include "f00.mm"
include "simplbi.mm"
include "syl.mm"
include "wrd0.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "impbii.mm"

theorem 0wrd0
  let cW: class W


  assert |- ( W e. Word (/) <-> W = (/) )

  proof
    cW
    c0
    cword
    #
    wcel
    #
    cW
    c0
    wceq
    #
    @1
    cc0
    cW
    chash
    cfv
    cfzo
    co
    #
    c0
    cW
    wf
    #
    @2
    c0
    cW
    wrdf
    @4
    @2
    @3
    c0
    wceq
    @3
    cW
    f00
    simplbi
    syl
    @2
    @1
    c0
    @0
    wcel
    c0
    wrd0
    cW
    c0
    @0
    eleq1
    mpbiri
    impbii
end
