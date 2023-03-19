include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "cwlkson.mm"
include "co.mm"
include "wceq.mm"
include "id.mm"
include "eqidd.mm"
include "cvtx.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "w3a.mm"
include "wb.mm"
include "eqid.mm"
include "wlkepvtx.mm"
include "wlkv.mm"
include "3simpc.mm"
include "syl.mm"
include "iswlkon.mm"
include "syl2anc.mm"
include "mpbir3and.mm"

theorem wlkonwlk
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Walks ` G ) P -> F ( ( P ` 0 ) ( WalksOn ` G ) ( P ` ( # ` F ) ) ) P )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    cP
    cc0
    cP
    cfv
    #
    cF
    chash
    cfv
    cP
    cfv
    #
    cG
    cwlkson
    cfv
    co
    wbr
    #
    @0
    @1
    @1
    wceq
    #
    @2
    @2
    wceq
    #
    @0
    id
    @0
    @1
    eqidd
    @0
    @2
    eqidd
    @0
    @1
    cG
    cvtx
    cfv
    #
    wcel
    @2
    @6
    wcel
    wa
    cF
    cvv
    wcel
    #
    cP
    cvv
    wcel
    #
    wa
    #
    @3
    @0
    @4
    @5
    w3a
    wb
    cP
    cF
    cG
    @6
    @6
    eqid
    #
    wlkepvtx
    @0
    cG
    cvv
    wcel
    #
    @7
    @8
    w3a
    @9
    cP
    cF
    cG
    wlkv
    @11
    @7
    @8
    3simpc
    syl
    @1
    @2
    cP
    cvv
    cF
    cG
    @6
    cvv
    @10
    iswlkon
    syl2anc
    mpbir3and
end
