include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wlkcl.mm"
include "eqid.mm"
include "wlkp.mm"
include "ffz0hash.mm"
include "syl2anc.mm"

theorem wlklenvp1
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Walks ` G ) P -> ( # ` P ) = ( ( # ` F ) + 1 ) )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cF
    chash
    cfv
    #
    cn0
    wcel
    cc0
    @0
    cfz
    co
    cG
    cvtx
    cfv
    #
    cP
    wf
    cP
    chash
    cfv
    @0
    c1
    caddc
    co
    wceq
    cP
    cF
    cG
    wlkcl
    cP
    cF
    cG
    @1
    @1
    eqid
    wlkp
    @1
    cP
    @0
    ffz0hash
    syl2anc
end
