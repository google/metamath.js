include "cc0.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cioo.mm"
include "wcel.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "csin.mm"
include "cfv.mm"
include "ccos.mm"
include "wa.mm"
include "cxr.mm"
include "wb.mm"
include "0xr.mm"
include "halfpire.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"
include "sincosq1lem.mm"
include "cmin.mm"
include "resubcl.mm"
include "mpan.mm"
include "syl3an1.mm"
include "3expib.mm"
include "0re.mm"
include "ltsub13.mm"
include "mp3an12.mm"
include "recni.mm"
include "subid1i.mm"
include "breq2i.mm"
include "syl6bb.mm"
include "ltsub23.mm"
include "mp3an13.mm"
include "subidi.mm"
include "breq1i.mm"
include "anbi12d.mm"
include "ancom.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "sinhalfpim.mm"
include "syl.mm"
include "breq2d.mm"
include "3imtr3d.mm"
include "3impib.mm"
include "jca.mm"
include "sylbi.mm"

theorem sincosq1sgn
  let cA: class A


  assert |- ( A e. ( 0 (,) ( _pi / 2 ) ) -> ( 0 < ( sin ` A ) /\ 0 < ( cos ` A ) ) )

  proof
    cA
    cc0
    cpi
    c2
    cdiv
    co
    #
    cioo
    co
    wcel
    #
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
    @0
    clt
    wbr
    #
    w3a
    #
    cc0
    cA
    csin
    cfv
    clt
    wbr
    #
    cc0
    cA
    ccos
    cfv
    #
    clt
    wbr
    #
    wa
    cc0
    cxr
    wcel
    @0
    cxr
    wcel
    @1
    @5
    wb
    0xr
    @0
    halfpire
    rexri
    cc0
    @0
    cA
    elioo2
    mp2an
    @5
    @6
    @8
    cA
    sincosq1lem
    @2
    @3
    @4
    @8
    @2
    cc0
    @0
    cA
    cmin
    co
    #
    clt
    wbr
    #
    @9
    @0
    clt
    wbr
    #
    wa
    #
    cc0
    @9
    csin
    cfv
    #
    clt
    wbr
    #
    @3
    @4
    wa
    #
    @8
    @2
    @10
    @11
    @14
    @2
    @9
    cr
    wcel
    #
    @10
    @11
    @14
    @0
    cr
    wcel
    #
    @2
    @16
    halfpire
    @0
    cA
    resubcl
    mpan
    @9
    sincosq1lem
    syl3an1
    3expib
    @2
    @12
    @4
    @3
    wa
    @15
    @2
    @10
    @4
    @11
    @3
    @2
    @10
    cA
    @0
    cc0
    cmin
    co
    #
    clt
    wbr
    #
    @4
    cc0
    cr
    wcel
    @17
    @2
    @10
    @19
    wb
    0re
    halfpire
    cc0
    @0
    cA
    ltsub13
    mp3an12
    @18
    @0
    cA
    clt
    @0
    @0
    halfpire
    recni
    #
    subid1i
    breq2i
    syl6bb
    @2
    @11
    @0
    @0
    cmin
    co
    #
    cA
    clt
    wbr
    #
    @3
    @17
    @2
    @17
    @11
    @22
    wb
    halfpire
    halfpire
    @0
    cA
    @0
    ltsub23
    mp3an13
    @21
    cc0
    cA
    clt
    @0
    @20
    subidi
    breq1i
    syl6bb
    anbi12d
    @4
    @3
    ancom
    syl6bb
    @2
    @13
    @7
    cc0
    clt
    @2
    cA
    cc
    wcel
    @13
    @7
    wceq
    cA
    recn
    cA
    sinhalfpim
    syl
    breq2d
    3imtr3d
    3impib
    jca
    sylbi
end
