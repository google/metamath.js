include "cword.mm"
include "wcel.mm"
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
include "ccatws1len.mm"
include "breqtrrd.mm"
include "cvv.mm"
include "wb.mm"
include "ovex.mm"
include "hashneq0.mm"
include "ax-mp.mm"
include "sylib.mm"

theorem ccatws1n0
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( W e. Word V -> ( W ++ <" X "> ) =/= (/) )

  proof
    cW
    cV
    cword
    wcel
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
    @2
    c0
    wne
    #
    @0
    cc0
    cW
    chash
    cfv
    #
    c1
    caddc
    co
    #
    @3
    clt
    @0
    @6
    cn0
    wcel
    cc0
    @7
    clt
    wbr
    cV
    cW
    lencl
    @6
    nn0p1gt0
    syl
    cV
    cW
    cX
    ccatws1len
    breqtrrd
    @2
    cvv
    wcel
    @4
    @5
    wb
    cW
    @1
    cconcat
    ovex
    @2
    cvv
    hashneq0
    ax-mp
    sylib
end
