include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cioo.mm"
include "wcel.mm"
include "cc0.mm"
include "cmin.mm"
include "csin.mm"
include "cfv.mm"
include "ccos.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "halfpire.mm"
include "elioore.mm"
include "resubcl.mm"
include "sylancr.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "neghalfpirx.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"
include "simp3bi.mm"
include "posdif.mm"
include "sylancl.mm"
include "mpbid.mm"
include "cc.mm"
include "picn.mm"
include "halfcl.mm"
include "ax-mp.mm"
include "negcli.mm"
include "caddc.mm"
include "negsubi.mm"
include "pidiv2halves.mm"
include "subaddrii.mm"
include "eqtri.mm"
include "simp2bi.mm"
include "syl5eqbr.mm"
include "pire.mm"
include "ltsub23.mm"
include "mp3an13.mm"
include "syl.mm"
include "mpbird.mm"
include "0xr.mm"
include "syl3anbrc.mm"
include "sinq12gt0.mm"
include "wceq.mm"
include "recnd.mm"
include "sinhalfpim.mm"
include "breqtrd.mm"

theorem cosq14gt0
  let cA: class A


  assert |- ( A e. ( -u ( _pi / 2 ) (,) ( _pi / 2 ) ) -> 0 < ( cos ` A ) )

  proof
    cA
    cpi
    c2
    cdiv
    co
    #
    cneg
    #
    @0
    cioo
    co
    wcel
    #
    cc0
    @0
    cA
    cmin
    co
    #
    csin
    cfv
    #
    cA
    ccos
    cfv
    #
    clt
    @2
    @3
    cc0
    cpi
    cioo
    co
    wcel
    #
    cc0
    @4
    clt
    wbr
    @2
    @3
    cr
    wcel
    #
    cc0
    @3
    clt
    wbr
    #
    @3
    cpi
    clt
    wbr
    #
    @6
    @2
    @0
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    @7
    halfpire
    cA
    @1
    @0
    elioore
    #
    @0
    cA
    resubcl
    sylancr
    @2
    cA
    @0
    clt
    wbr
    #
    @8
    @2
    @11
    @1
    cA
    clt
    wbr
    #
    @13
    @1
    cxr
    wcel
    @0
    cxr
    wcel
    @2
    @11
    @14
    @13
    w3a
    wb
    neghalfpirx
    @0
    halfpire
    rexri
    @1
    @0
    cA
    elioo2
    mp2an
    #
    simp3bi
    @2
    @11
    @10
    @13
    @8
    wb
    @12
    halfpire
    cA
    @0
    posdif
    sylancl
    mpbid
    @2
    @9
    @0
    cpi
    cmin
    co
    #
    cA
    clt
    wbr
    #
    @2
    @16
    @1
    cA
    clt
    @0
    cpi
    @1
    cpi
    cc
    wcel
    @0
    cc
    wcel
    picn
    cpi
    halfcl
    ax-mp
    #
    picn
    @0
    @18
    negcli
    cpi
    @1
    caddc
    co
    cpi
    @0
    cmin
    co
    @0
    cpi
    @0
    picn
    @18
    negsubi
    cpi
    @0
    @0
    picn
    @18
    @18
    pidiv2halves
    subaddrii
    eqtri
    subaddrii
    @2
    @11
    @14
    @13
    @15
    simp2bi
    syl5eqbr
    @2
    @11
    @9
    @17
    wb
    #
    @12
    @10
    @11
    cpi
    cr
    wcel
    @19
    halfpire
    pire
    @0
    cA
    cpi
    ltsub23
    mp3an13
    syl
    mpbird
    cc0
    cxr
    wcel
    cpi
    cxr
    wcel
    @6
    @7
    @8
    @9
    w3a
    wb
    0xr
    cpi
    pire
    rexri
    cc0
    cpi
    @3
    elioo2
    mp2an
    syl3anbrc
    @3
    sinq12gt0
    syl
    @2
    cA
    cc
    wcel
    @4
    @5
    wceq
    @2
    cA
    @12
    recnd
    cA
    sinhalfpim
    syl
    breqtrd
end
