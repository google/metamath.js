include "cc0.mm"
include "cpi.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "csin.mm"
include "cfv.mm"
include "cle.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "cr.mm"
include "0re.mm"
include "pire.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "w3a.mm"
include "cioo.mm"
include "wb.mm"
include "cxr.mm"
include "rexr.mm"
include "elioo2.mm"
include "syl2an.mm"
include "mp2an.mm"
include "sinq12gt0.mm"
include "sylbir.mm"
include "3expib.mm"
include "syl.mm"
include "resincld.mm"
include "ltle.mm"
include "sylancr.mm"
include "syld.mm"
include "expd.mm"
include "0le0.mm"
include "sin0.mm"
include "breqtrri.mm"
include "fveq2.mm"
include "syl5breq.mm"
include "a1d.mm"
include "a1i.mm"
include "wo.mm"
include "simp2bi.mm"
include "leloe.mm"
include "mpbid.mm"
include "mpjaod.mm"
include "sinpi.mm"
include "syl5breqr.mm"
include "simp3bi.mm"
include "sylancl.mm"

theorem sinq12ge0
  let cA: class A


  assert |- ( A e. ( 0 [,] _pi ) -> 0 <_ ( sin ` A ) )

  proof
    cA
    cc0
    cpi
    cicc
    co
    wcel
    #
    cA
    cpi
    clt
    wbr
    #
    cc0
    cA
    csin
    cfv
    #
    cle
    wbr
    #
    cA
    cpi
    wceq
    #
    @0
    cc0
    cA
    clt
    wbr
    #
    @1
    @3
    wi
    #
    cc0
    cA
    wceq
    #
    @0
    @5
    @1
    @3
    @0
    @5
    @1
    wa
    #
    cc0
    @2
    clt
    wbr
    #
    @3
    @0
    cA
    cr
    wcel
    #
    @8
    @9
    wi
    @0
    @10
    cc0
    cA
    cle
    wbr
    #
    cA
    cpi
    cle
    wbr
    #
    cc0
    cpi
    cA
    0re
    pire
    elicc2i
    #
    simp1bi
    #
    @10
    @5
    @1
    @9
    @10
    @5
    @1
    w3a
    #
    cA
    cc0
    cpi
    cioo
    co
    wcel
    #
    @9
    cc0
    cr
    wcel
    #
    cpi
    cr
    wcel
    #
    @16
    @15
    wb
    #
    0re
    pire
    @17
    cc0
    cxr
    wcel
    cpi
    cxr
    wcel
    @19
    @18
    cc0
    rexr
    cpi
    rexr
    cc0
    cpi
    cA
    elioo2
    syl2an
    mp2an
    cA
    sinq12gt0
    sylbir
    3expib
    syl
    @0
    @17
    @2
    cr
    wcel
    @9
    @3
    wi
    0re
    @0
    cA
    @14
    resincld
    cc0
    @2
    ltle
    sylancr
    syld
    expd
    @7
    @6
    wi
    @0
    @7
    @3
    @1
    @7
    cc0
    cc0
    csin
    cfv
    #
    @2
    cle
    cc0
    cc0
    @20
    cle
    0le0
    sin0
    breqtrri
    cc0
    cA
    csin
    fveq2
    syl5breq
    a1d
    a1i
    @0
    @11
    @5
    @7
    wo
    #
    @0
    @10
    @11
    @12
    @13
    simp2bi
    @0
    @17
    @10
    @11
    @21
    wb
    0re
    @14
    cc0
    cA
    leloe
    sylancr
    mpbid
    mpjaod
    @4
    @3
    wi
    @0
    @4
    cc0
    cpi
    csin
    cfv
    #
    @2
    cle
    cc0
    cc0
    @22
    cle
    0le0
    sinpi
    breqtrri
    cA
    cpi
    csin
    fveq2
    syl5breqr
    a1i
    @0
    @12
    @1
    @4
    wo
    #
    @0
    @10
    @11
    @12
    @13
    simp3bi
    @0
    @10
    @18
    @12
    @23
    wb
    @14
    pire
    cA
    cpi
    leloe
    sylancl
    mpbid
    mpjaod
end
