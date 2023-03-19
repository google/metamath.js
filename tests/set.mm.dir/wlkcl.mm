include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cn0.mm"
include "eqid.mm"
include "wlkf.mm"
include "lencl.mm"
include "syl.mm"

theorem wlkcl
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Walks ` G ) P -> ( # ` F ) e. NN0 )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cF
    cG
    ciedg
    cfv
    #
    cdm
    #
    cword
    wcel
    cF
    chash
    cfv
    cn0
    wcel
    cP
    cF
    cG
    @0
    @0
    eqid
    wlkf
    @1
    cF
    lencl
    syl
end
