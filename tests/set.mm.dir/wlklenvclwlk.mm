include "cc0.mm"
include "cfv.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cop.mm"
include "cwlks.mm"
include "wcel.mm"
include "cvtx.mm"
include "cword.mm"
include "c1.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "df-br.mm"
include "caddc.mm"
include "cn0.mm"
include "wlklenvp1.mm"
include "wlkcl.mm"
include "wrdsymb1.mm"
include "s1cld.mm"
include "ccatlen.mm"
include "syldan.mm"
include "s1len.mm"
include "a1i.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "lencl.mm"
include "eqcom.mm"
include "cc.mm"
include "nn0cn.mm"
include "adantl.mm"
include "adantr.mm"
include "1cnd.mm"
include "addcan2d.mm"
include "biimpd.mm"
include "syl5bi.mm"
include "ex.mm"
include "com23.mm"
include "syl.mm"
include "sylbid.mm"
include "com3l.mm"
include "sylc.mm"
include "sylbir.mm"
include "com12.mm"

theorem wlklenvclwlk
  let cF: class F
  let cG: class G
  let cW: class W


  assert |- ( ( W e. Word ( Vtx ` G ) /\ 1 <_ ( # ` W ) ) -> ( <. F , ( W ++ <" ( W ` 0 ) "> ) >. e. ( Walks ` G ) -> ( # ` F ) = ( # ` W ) ) )

  proof
    cF
    cW
    cc0
    cW
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    cop
    cG
    cwlks
    cfv
    #
    wcel
    #
    cW
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    c1
    cW
    chash
    cfv
    #
    cle
    wbr
    #
    wa
    #
    cF
    chash
    cfv
    #
    @8
    wceq
    #
    @4
    cF
    @2
    @3
    wbr
    #
    @10
    @12
    wi
    #
    cF
    @2
    @3
    df-br
    @13
    @2
    chash
    cfv
    #
    @11
    c1
    caddc
    co
    #
    wceq
    #
    @11
    cn0
    wcel
    #
    @14
    @2
    cF
    cG
    wlklenvp1
    @2
    cF
    cG
    wlkcl
    @10
    @17
    @18
    @12
    @10
    @17
    @8
    c1
    caddc
    co
    #
    @16
    wceq
    #
    @18
    @12
    wi
    #
    @10
    @15
    @19
    @16
    @10
    @15
    @8
    @1
    chash
    cfv
    #
    caddc
    co
    #
    @19
    @7
    @9
    @1
    @6
    wcel
    @15
    @23
    wceq
    @10
    @0
    @5
    @5
    cW
    wrdsymb1
    s1cld
    @5
    cW
    @1
    ccatlen
    syldan
    @10
    @22
    c1
    @8
    caddc
    @22
    c1
    wceq
    @10
    @0
    s1len
    a1i
    oveq2d
    eqtrd
    eqeq1d
    @7
    @20
    @21
    wi
    #
    @9
    @7
    @8
    cn0
    wcel
    #
    @24
    @5
    cW
    lencl
    @25
    @18
    @20
    @12
    @25
    @18
    @20
    @12
    wi
    @20
    @16
    @19
    wceq
    #
    @25
    @18
    wa
    #
    @12
    @19
    @16
    eqcom
    @27
    @26
    @12
    @27
    @11
    @8
    c1
    @18
    @11
    cc
    wcel
    @25
    @11
    nn0cn
    adantl
    @25
    @8
    cc
    wcel
    @18
    @8
    nn0cn
    adantr
    @27
    1cnd
    addcan2d
    biimpd
    syl5bi
    ex
    com23
    syl
    adantr
    sylbid
    com3l
    sylc
    sylbir
    com12
end
