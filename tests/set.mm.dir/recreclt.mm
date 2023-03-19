include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "recgt0.mm"
include "wb.mm"
include "wne.mm"
include "gt0ne0.mm"
include "rereccl.mm"
include "syldan.mm"
include "1re.mm"
include "ltaddpos.mm"
include "sylancl.mm"
include "mpbid.mm"
include "readdcl.mm"
include "sylancr.mm"
include "0lt1.mm"
include "wi.mm"
include "0re.mm"
include "lttr.mm"
include "mp3an12.mm"
include "syl.mm"
include "mpani.mm"
include "mpd.mm"
include "recgt1.mm"
include "syl2anc.mm"
include "mpbii.mm"
include "cc.mm"
include "wceq.mm"
include "recnd.mm"
include "ax-1cn.mm"
include "addcom.mm"
include "breqtrd.mm"
include "simpl.mm"
include "simpr.mm"
include "ltrec1.mm"
include "syl22anc.mm"
include "jca.mm"

theorem recreclt
  let cA: class A


  assert |- ( ( A e. RR /\ 0 < A ) -> ( ( 1 / ( 1 + ( 1 / A ) ) ) < 1 /\ ( 1 / ( 1 + ( 1 / A ) ) ) < A ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    c1
    c1
    c1
    cA
    cdiv
    co
    #
    caddc
    co
    #
    cdiv
    co
    #
    c1
    clt
    wbr
    #
    @5
    cA
    clt
    wbr
    #
    @2
    c1
    @4
    clt
    wbr
    #
    @6
    @2
    cc0
    @3
    clt
    wbr
    #
    @8
    cA
    recgt0
    @2
    @3
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @9
    @8
    wb
    @0
    @1
    cA
    cc0
    wne
    @10
    cA
    gt0ne0
    cA
    rereccl
    syldan
    #
    1re
    @3
    c1
    ltaddpos
    sylancl
    mpbid
    #
    @2
    @4
    cr
    wcel
    #
    cc0
    @4
    clt
    wbr
    #
    @8
    @6
    wb
    @2
    @11
    @10
    @14
    1re
    @12
    c1
    @3
    readdcl
    sylancr
    #
    @2
    @8
    @15
    @13
    @2
    cc0
    c1
    clt
    wbr
    #
    @8
    @15
    0lt1
    @2
    @14
    @17
    @8
    wa
    @15
    wi
    #
    @16
    cc0
    cr
    wcel
    @11
    @14
    @18
    0re
    1re
    cc0
    c1
    @4
    lttr
    mp3an12
    syl
    mpani
    mpd
    #
    @4
    recgt1
    syl2anc
    mpbid
    @2
    @3
    @4
    clt
    wbr
    #
    @7
    @2
    @3
    @3
    c1
    caddc
    co
    #
    @4
    clt
    @2
    @17
    @3
    @21
    clt
    wbr
    #
    0lt1
    @2
    @11
    @10
    @17
    @22
    wb
    1re
    @12
    c1
    @3
    ltaddpos
    sylancr
    mpbii
    @2
    @3
    cc
    wcel
    c1
    cc
    wcel
    @21
    @4
    wceq
    @2
    @3
    @12
    recnd
    ax-1cn
    @3
    c1
    addcom
    sylancl
    breqtrd
    @2
    @0
    @1
    @14
    @15
    @20
    @7
    wb
    @0
    @1
    simpl
    @0
    @1
    simpr
    @16
    @19
    cA
    @4
    ltrec1
    syl22anc
    mpbid
    jca
end
