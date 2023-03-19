include "ctrls.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "ctrlson.mm"
include "co.mm"
include "cwlkson.mm"
include "cwlks.mm"
include "trliswlk.mm"
include "wlkonwlk.mm"
include "syl.mm"
include "id.mm"
include "cvtx.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "wb.mm"
include "w3a.mm"
include "eqid.mm"
include "wlkepvtx.mm"
include "wlkv.mm"
include "simpll.mm"
include "simplr.mm"
include "jca.mm"
include "3simpc.mm"
include "adantl.mm"
include "syl2anc.mm"
include "istrlson.mm"
include "mpbir2and.mm"

theorem trlontrl
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Trails ` G ) P -> F ( ( P ` 0 ) ( TrailsOn ` G ) ( P ` ( # ` F ) ) ) P )

  proof
    cF
    cP
    cG
    ctrls
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
    ctrlson
    cfv
    co
    wbr
    #
    cF
    cP
    @1
    @2
    cG
    cwlkson
    cfv
    co
    wbr
    #
    @0
    @0
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @4
    cP
    cF
    cG
    trliswlk
    #
    cP
    cF
    cG
    wlkonwlk
    syl
    @0
    id
    @0
    @1
    cG
    cvtx
    cfv
    #
    wcel
    #
    @2
    @7
    wcel
    #
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
    #
    @3
    @4
    @0
    wa
    wb
    @0
    @5
    @14
    @6
    @5
    @10
    cG
    cvv
    wcel
    #
    @11
    @12
    w3a
    #
    @14
    cP
    cF
    cG
    @7
    @7
    eqid
    #
    wlkepvtx
    cP
    cF
    cG
    wlkv
    @10
    @16
    wa
    #
    @10
    @13
    @18
    @8
    @9
    @8
    @9
    @16
    simpll
    @8
    @9
    @16
    simplr
    jca
    @16
    @13
    @10
    @15
    @11
    @12
    3simpc
    adantl
    jca
    syl2anc
    syl
    @1
    @2
    cP
    cvv
    cF
    cG
    @7
    cvv
    @17
    istrlson
    syl
    mpbir2and
end
