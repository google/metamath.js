include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "csin.mm"
include "cfv.mm"
include "wi.mm"
include "halfpire.mm"
include "ltle.mm"
include "mpan2.mm"
include "c4.mm"
include "pire.mm"
include "4re.mm"
include "pigt2lt4.mm"
include "simpri.mm"
include "ltleii.mm"
include "cmul.mm"
include "wa.mm"
include "wb.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "ledivmul.mm"
include "mp3an.mm"
include "2t2e4.mm"
include "breq2i.mm"
include "bitri.mm"
include "mpbir.mm"
include "letr.mm"
include "mp3an23.mm"
include "mpan2i.mm"
include "syld.mm"
include "adantr.mm"
include "3impia.mm"
include "w3a.mm"
include "cioc.mm"
include "cxr.mm"
include "0xr.mm"
include "elioc2.mm"
include "mp2an.mm"
include "sin02gt0.mm"
include "sylbir.mm"
include "syld3an3.mm"

theorem sincosq1lem
  let cA: class A


  assert |- ( ( A e. RR /\ 0 < A /\ A < ( _pi / 2 ) ) -> 0 < ( sin ` A ) )

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
    cA
    cpi
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    cA
    c2
    cle
    wbr
    #
    cc0
    cA
    csin
    cfv
    clt
    wbr
    #
    @0
    @1
    @3
    @4
    @0
    @3
    @4
    wi
    @1
    @0
    @3
    cA
    @2
    cle
    wbr
    #
    @4
    @0
    @2
    cr
    wcel
    #
    @3
    @6
    wi
    halfpire
    cA
    @2
    ltle
    mpan2
    @0
    @6
    @2
    c2
    cle
    wbr
    #
    @4
    @8
    cpi
    c4
    cle
    wbr
    #
    cpi
    c4
    pire
    4re
    c2
    cpi
    clt
    wbr
    cpi
    c4
    clt
    wbr
    pigt2lt4
    simpri
    ltleii
    @8
    cpi
    c2
    c2
    cmul
    co
    #
    cle
    wbr
    #
    @9
    cpi
    cr
    wcel
    c2
    cr
    wcel
    #
    @12
    cc0
    c2
    clt
    wbr
    #
    wa
    @8
    @11
    wb
    pire
    2re
    @12
    @13
    2re
    2pos
    pm3.2i
    cpi
    c2
    c2
    ledivmul
    mp3an
    @10
    c4
    cpi
    cle
    2t2e4
    breq2i
    bitri
    mpbir
    @0
    @7
    @12
    @6
    @8
    wa
    @4
    wi
    halfpire
    2re
    cA
    @2
    c2
    letr
    mp3an23
    mpan2i
    syld
    adantr
    3impia
    @0
    @1
    @4
    w3a
    #
    cA
    cc0
    c2
    cioc
    co
    wcel
    #
    @5
    cc0
    cxr
    wcel
    @12
    @15
    @14
    wb
    0xr
    2re
    cc0
    c2
    cA
    elioc2
    mp2an
    cA
    sin02gt0
    sylbir
    syld3an3
end
