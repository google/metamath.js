include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "c1.mm"
include "cle.mm"
include "hashneq0.mm"
include "cz.mm"
include "wb.mm"
include "lencl.mm"
include "nn0zd.mm"
include "zgt0ge1.mm"
include "syl.mm"
include "bitr3d.mm"

theorem wrdlenge1n0
  let cV: class V
  let cW: class W


  assert |- ( W e. Word V -> ( W =/= (/) <-> 1 <_ ( # ` W ) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cc0
    cW
    chash
    cfv
    #
    clt
    wbr
    #
    cW
    c0
    wne
    c1
    @2
    cle
    wbr
    #
    cW
    @0
    hashneq0
    @1
    @2
    cz
    wcel
    @3
    @4
    wb
    @1
    @2
    cV
    cW
    lencl
    nn0zd
    @2
    zgt0ge1
    syl
    bitr3d
end
