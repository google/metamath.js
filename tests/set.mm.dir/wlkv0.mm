include "cvtx.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cwlks.mm"
include "wcel.mm"
include "c1st.mm"
include "c2nd.mm"
include "wa.mm"
include "wbr.mm"
include "wlkcpr.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "eqid.mm"
include "wlkf.mm"
include "wlkp.mm"
include "jca.mm"
include "wi.mm"
include "feq3.mm"
include "f00.mm"
include "syl6bb.mm"
include "cn0.mm"
include "clt.mm"
include "cz.mm"
include "wb.mm"
include "0z.mm"
include "nn0z.mm"
include "fzn.mm"
include "sylancr.mm"
include "nn0nlt0.mm"
include "pm2.21d.mm"
include "sylbird.mm"
include "com12.mm"
include "adantl.mm"
include "lencl.mm"
include "impel.mm"
include "simpll.mm"
include "ex.mm"
include "syl6bi.mm"
include "com23.mm"
include "impd.mm"
include "syl5.mm"
include "syl5bi.mm"
include "imp.mm"

theorem wlkv0
  let cG: class G
  let cW: class W


  assert |- ( ( ( Vtx ` G ) = (/) /\ W e. ( Walks ` G ) ) -> ( ( 1st ` W ) = (/) /\ ( 2nd ` W ) = (/) ) )

  proof
    cG
    cvtx
    cfv
    #
    c0
    wceq
    #
    cW
    cG
    cwlks
    cfv
    #
    wcel
    #
    cW
    c1st
    cfv
    #
    c0
    wceq
    #
    cW
    c2nd
    cfv
    #
    c0
    wceq
    #
    wa
    #
    @3
    @4
    @6
    @2
    wbr
    #
    @1
    @8
    cG
    cW
    wlkcpr
    @9
    @4
    cG
    ciedg
    cfv
    #
    cdm
    #
    cword
    wcel
    #
    cc0
    @4
    chash
    cfv
    #
    cfz
    co
    #
    @0
    @6
    wf
    #
    wa
    @1
    @8
    @9
    @12
    @15
    @6
    @4
    cG
    @10
    @10
    eqid
    wlkf
    @6
    @4
    cG
    @0
    @0
    eqid
    wlkp
    jca
    @1
    @12
    @15
    @8
    @1
    @15
    @12
    @8
    @1
    @15
    @7
    @14
    c0
    wceq
    #
    wa
    #
    @12
    @8
    wi
    @1
    @15
    @14
    c0
    @6
    wf
    @17
    @0
    c0
    @14
    @6
    feq3
    @14
    @6
    f00
    syl6bb
    @17
    @12
    @8
    @17
    @12
    wa
    @5
    @7
    @17
    @13
    cn0
    wcel
    #
    @5
    @12
    @16
    @18
    @5
    wi
    @7
    @18
    @16
    @5
    @18
    @16
    @13
    cc0
    clt
    wbr
    #
    @5
    @18
    cc0
    cz
    wcel
    @13
    cz
    wcel
    @19
    @16
    wb
    0z
    @13
    nn0z
    cc0
    @13
    fzn
    sylancr
    @18
    @19
    @5
    @13
    nn0nlt0
    pm2.21d
    sylbird
    com12
    adantl
    @11
    @4
    lencl
    impel
    @7
    @16
    @12
    simpll
    jca
    ex
    syl6bi
    com23
    impd
    syl5
    syl5bi
    imp
end
