include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "clt.mm"
include "wb.mm"
include "cv.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "odd2np1.mm"
include "wa.mm"
include "cc0.mm"
include "cioo.mm"
include "cxr.mm"
include "w3a.mm"
include "0xr.mm"
include "1re.mm"
include "rexri.mm"
include "halfre.mm"
include "3pm3.2i.mm"
include "halfgt0.mm"
include "halflt1.mm"
include "pm3.2i.mm"
include "elioo3g.mm"
include "mpbir2an.mm"
include "zltaddlt1le.mm"
include "mp3an3.mm"
include "cc.mm"
include "wne.mm"
include "zcn.mm"
include "adantr.mm"
include "1cnd.mm"
include "2cnne0.mm"
include "a1i.mm"
include "muldivdir.mm"
include "syl3anc.mm"
include "breq1d.mm"
include "3bitr4rd.mm"
include "oveq1.mm"
include "bibi12d.mm"
include "syl5ibcom.mm"
include "ex.mm"
include "adantl.mm"
include "com23.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "3imp.mm"

theorem halfleoddlt
  let cM: class M
  let cN: class N
  let vn: setvar n


  assert |- ( ( N e. ZZ /\ -. 2 || N /\ M e. ZZ ) -> ( ( N / 2 ) <_ M <-> ( N / 2 ) < M ) )

  proof
    cN
    cz
    wcel
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    cM
    cz
    wcel
    #
    cN
    c2
    cdiv
    co
    #
    cM
    cle
    wbr
    #
    @3
    cM
    clt
    wbr
    #
    wb
    #
    @0
    @1
    c2
    vn
    cv
    #
    cmul
    co
    c1
    caddc
    co
    #
    cN
    wceq
    #
    vn
    cz
    wrex
    @2
    @6
    wi
    #
    vn
    cN
    odd2np1
    @0
    @9
    @10
    vn
    cz
    @0
    @7
    cz
    wcel
    #
    wa
    @2
    @9
    @6
    @11
    @2
    @9
    @6
    wi
    #
    wi
    @0
    @11
    @2
    @12
    @11
    @2
    wa
    #
    @8
    c2
    cdiv
    co
    #
    cM
    cle
    wbr
    #
    @14
    cM
    clt
    wbr
    #
    wb
    @9
    @6
    @13
    @7
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cM
    clt
    wbr
    #
    @18
    cM
    cle
    wbr
    #
    @16
    @15
    @11
    @2
    @17
    cc0
    c1
    cioo
    co
    wcel
    #
    @19
    @20
    wb
    @21
    cc0
    cxr
    wcel
    #
    c1
    cxr
    wcel
    #
    @17
    cxr
    wcel
    #
    w3a
    cc0
    @17
    clt
    wbr
    #
    @17
    c1
    clt
    wbr
    #
    wa
    @22
    @23
    @24
    0xr
    c1
    1re
    rexri
    @17
    halfre
    rexri
    3pm3.2i
    @25
    @26
    halfgt0
    halflt1
    pm3.2i
    cc0
    c1
    @17
    elioo3g
    mpbir2an
    @17
    @7
    cM
    zltaddlt1le
    mp3an3
    @13
    @14
    @18
    cM
    clt
    @13
    @7
    cc
    wcel
    #
    c1
    cc
    wcel
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    #
    @14
    @18
    wceq
    @11
    @27
    @2
    @7
    zcn
    adantr
    @13
    1cnd
    @28
    @13
    2cnne0
    a1i
    @7
    c1
    c2
    muldivdir
    syl3anc
    #
    breq1d
    @13
    @14
    @18
    cM
    cle
    @29
    breq1d
    3bitr4rd
    @9
    @15
    @4
    @16
    @5
    @9
    @14
    @3
    cM
    cle
    @8
    cN
    c2
    cdiv
    oveq1
    #
    breq1d
    @9
    @14
    @3
    cM
    clt
    @30
    breq1d
    bibi12d
    syl5ibcom
    ex
    adantl
    com23
    rexlimdva
    sylbid
    3imp
end
