include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "wlkp.mm"
include "wlkcl.mm"
include "0elfz.mm"
include "ffvelrn.mm"
include "sylan2.mm"
include "nn0fz0.mm"
include "sylan2b.mm"
include "jca.mm"
include "syl2anc.mm"

theorem wlkepvtx
  let cP: class P
  let cF: class F
  let cG: class G
  let cV: class V
  assume wlkpvtx.v: |- V = ( Vtx ` G )


  assert |- ( F ( Walks ` G ) P -> ( ( P ` 0 ) e. V /\ ( P ` ( # ` F ) ) e. V ) )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    #
    cV
    cP
    wf
    #
    @0
    cn0
    wcel
    #
    cc0
    cP
    cfv
    cV
    wcel
    #
    @0
    cP
    cfv
    cV
    wcel
    #
    wa
    cP
    cF
    cG
    cV
    wlkpvtx.v
    wlkp
    cP
    cF
    cG
    wlkcl
    @2
    @3
    wa
    @4
    @5
    @3
    @2
    cc0
    @1
    wcel
    @4
    @0
    0elfz
    @1
    cV
    cc0
    cP
    ffvelrn
    sylan2
    @3
    @2
    @0
    @1
    wcel
    @5
    @0
    nn0fz0
    @1
    cV
    @0
    cP
    ffvelrn
    sylan2b
    jca
    syl2anc
end
