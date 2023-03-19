include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "c1.mm"
include "caddc.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0p1gt0.mm"
include "syl.mm"
include "adantr.mm"
include "ccatws1lenOLD.mm"
include "breqtrrd.mm"
include "cvv.mm"
include "wb.mm"
include "ovex.mm"
include "hashneq0.mm"
include "ax-mp.mm"
include "sylib.mm"

theorem ccatws1n0OLD
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( W e. Word V /\ X e. V ) -> ( W ++ <" X "> ) =/= (/) )

  proof
    cW
    cV
    cword
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    cc0
    cW
    cX
    cs1
    #
    cconcat
    co
    #
    chash
    cfv
    #
    clt
    wbr
    #
    @4
    c0
    wne
    #
    @2
    cc0
    cW
    chash
    cfv
    #
    c1
    caddc
    co
    #
    @5
    clt
    @0
    cc0
    @9
    clt
    wbr
    #
    @1
    @0
    @8
    cn0
    wcel
    @10
    cV
    cW
    lencl
    @8
    nn0p1gt0
    syl
    adantr
    cV
    cW
    cX
    ccatws1lenOLD
    breqtrrd
    @4
    cvv
    wcel
    @6
    @7
    wb
    cW
    @3
    cconcat
    ovex
    @4
    cvv
    hashneq0
    ax-mp
    sylib
end
