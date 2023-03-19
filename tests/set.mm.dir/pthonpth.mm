include "cpths.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "cpthson.mm"
include "co.mm"
include "ctrlson.mm"
include "ctrls.mm"
include "pthistrl.mm"
include "trlontrl.mm"
include "syl.mm"
include "id.mm"
include "cwlks.mm"
include "cvtx.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "wb.mm"
include "pthiswlk.mm"
include "eqid.mm"
include "wlkepvtx.mm"
include "w3a.mm"
include "wlkv.mm"
include "3simpc.mm"
include "jca.mm"
include "ispthson.mm"
include "3syl.mm"
include "mpbir2and.mm"

theorem pthonpth
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Paths ` G ) P -> F ( ( P ` 0 ) ( PathsOn ` G ) ( P ` ( # ` F ) ) ) P )

  proof
    cF
    cP
    cG
    cpths
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
    cpthson
    cfv
    co
    wbr
    #
    cF
    cP
    @1
    @2
    cG
    ctrlson
    cfv
    co
    wbr
    #
    @0
    @0
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    @4
    cP
    cF
    cG
    pthistrl
    cP
    cF
    cG
    trlontrl
    syl
    @0
    id
    @0
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
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
    #
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
    wa
    @3
    @4
    @0
    wa
    wb
    cP
    cF
    cG
    pthiswlk
    @5
    @7
    @10
    cP
    cF
    cG
    @6
    @6
    eqid
    #
    wlkepvtx
    @5
    cG
    cvv
    wcel
    #
    @8
    @9
    w3a
    @10
    cP
    cF
    cG
    wlkv
    @12
    @8
    @9
    3simpc
    syl
    jca
    @1
    @2
    cP
    cvv
    cF
    cG
    @6
    cvv
    @11
    ispthson
    3syl
    mpbir2and
end
