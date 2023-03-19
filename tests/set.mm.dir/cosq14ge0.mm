include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cicc.mm"
include "wcel.mm"
include "cc0.mm"
include "cmin.mm"
include "csin.mm"
include "cfv.mm"
include "ccos.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "halfpire.mm"
include "neghalfpire.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "resubcl.mm"
include "sylancr.mm"
include "simp3bi.mm"
include "wb.mm"
include "subge0.mm"
include "mpbird.mm"
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
include "suble.mm"
include "mp3an13.mm"
include "syl.mm"
include "0re.mm"
include "syl3anbrc.mm"
include "sinq12ge0.mm"
include "wceq.mm"
include "recnd.mm"
include "sinhalfpim.mm"
include "breqtrd.mm"

theorem cosq14ge0
  let cA: class A


  assert |- ( A e. ( -u ( _pi / 2 ) [,] ( _pi / 2 ) ) -> 0 <_ ( cos ` A ) )

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
    cicc
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
    cle
    @2
    @3
    cc0
    cpi
    cicc
    co
    wcel
    #
    cc0
    @4
    cle
    wbr
    @2
    @3
    cr
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    @3
    cpi
    cle
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
    @2
    @11
    @1
    cA
    cle
    wbr
    #
    cA
    @0
    cle
    wbr
    #
    @1
    @0
    cA
    neghalfpire
    halfpire
    elicc2i
    #
    simp1bi
    #
    @0
    cA
    resubcl
    sylancr
    @2
    @8
    @13
    @2
    @11
    @12
    @13
    @14
    simp3bi
    @2
    @10
    @11
    @8
    @13
    wb
    halfpire
    @15
    @0
    cA
    subge0
    sylancr
    mpbird
    @2
    @9
    @0
    cpi
    cmin
    co
    #
    cA
    cle
    wbr
    #
    @2
    @16
    @1
    cA
    cle
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
    @12
    @13
    @14
    simp2bi
    syl5eqbr
    @2
    @11
    @9
    @17
    wb
    #
    @15
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
    suble
    mp3an13
    syl
    mpbird
    cc0
    cpi
    @3
    0re
    pire
    elicc2i
    syl3anbrc
    @3
    sinq12ge0
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
    @15
    recnd
    cA
    sinhalfpim
    syl
    breqtrd
end
