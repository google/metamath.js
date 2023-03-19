include "cc0.mm"
include "c1.mm"
include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "c3.mm"
include "cexp.mm"
include "cdiv.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "csin.mm"
include "cfv.mm"
include "cr.mm"
include "cn0.mm"
include "cle.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "1re.mm"
include "elioc2.mm"
include "mp2an.mm"
include "simp1bi.mm"
include "3nn0.mm"
include "reexpcl.mm"
include "sylancl.mm"
include "wne.mm"
include "3re.mm"
include "3ne0.mm"
include "redivcl.mm"
include "mp3an23.mm"
include "syl.mm"
include "cz.mm"
include "3z.mm"
include "expgt0.mm"
include "mp3an2.mm"
include "3adant3.mm"
include "sylbi.mm"
include "wa.mm"
include "0lt1.mm"
include "pm3.2i.mm"
include "3pos.mm"
include "1lt3.mm"
include "ltdiv2.mm"
include "mpbii.mm"
include "mp3an12.mm"
include "ex.mm"
include "sylc.mm"
include "recnd.mm"
include "div1d.mm"
include "breqtrd.mm"
include "1nn0.mm"
include "a1i.mm"
include "cuz.mm"
include "1le3.mm"
include "1z.mm"
include "eluz1i.mm"
include "mpbir2an.mm"
include "simp2bi.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "sylancr.mm"
include "mpd.mm"
include "simp3bi.mm"
include "leexp2rd.mm"
include "exp1d.mm"
include "ltletrd.mm"
include "posdifd.mm"
include "mpbid.mm"
include "sin01bnd.mm"
include "simpld.mm"
include "resubcld.mm"
include "resincld.mm"
include "lttr.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "mp2and.mm"

theorem sin01gt0
  let cA: class A


  assert |- ( A e. ( 0 (,] 1 ) -> 0 < ( sin ` A ) )

  proof
    cA
    cc0
    c1
    cioc
    co
    wcel
    #
    cc0
    cA
    cA
    c3
    cexp
    co
    #
    c3
    cdiv
    co
    #
    cmin
    co
    #
    clt
    wbr
    #
    @3
    cA
    csin
    cfv
    #
    clt
    wbr
    #
    cc0
    @5
    clt
    wbr
    #
    @0
    @2
    cA
    clt
    wbr
    @4
    @0
    @2
    @1
    cA
    @0
    @1
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    @0
    cA
    cr
    wcel
    #
    c3
    cn0
    wcel
    @8
    @0
    @10
    cc0
    cA
    clt
    wbr
    #
    cA
    c1
    cle
    wbr
    #
    cc0
    cxr
    wcel
    c1
    cr
    wcel
    #
    @0
    @10
    @11
    @12
    w3a
    #
    wb
    0xr
    1re
    cc0
    c1
    cA
    elioc2
    mp2an
    #
    simp1bi
    #
    3nn0
    cA
    c3
    reexpcl
    sylancl
    #
    @8
    c3
    cr
    wcel
    #
    c3
    cc0
    wne
    @9
    3re
    3ne0
    @1
    c3
    redivcl
    mp3an23
    syl
    #
    @17
    @16
    @0
    @2
    @1
    c1
    cdiv
    co
    #
    @1
    clt
    @0
    @8
    cc0
    @1
    clt
    wbr
    #
    @2
    @20
    clt
    wbr
    #
    @17
    @0
    @14
    @21
    @15
    @10
    @11
    @21
    @12
    @10
    c3
    cz
    wcel
    #
    @11
    @21
    3z
    cA
    c3
    expgt0
    mp3an2
    3adant3
    sylbi
    @8
    @21
    @22
    @13
    cc0
    c1
    clt
    wbr
    #
    wa
    #
    @18
    cc0
    c3
    clt
    wbr
    #
    wa
    #
    @8
    @21
    wa
    #
    @22
    @13
    @24
    1re
    0lt1
    pm3.2i
    @18
    @26
    3re
    3pos
    pm3.2i
    @25
    @27
    @28
    w3a
    c1
    c3
    clt
    wbr
    @22
    1lt3
    c1
    c3
    @1
    ltdiv2
    mpbii
    mp3an12
    ex
    sylc
    @0
    @1
    @0
    @1
    @17
    recnd
    div1d
    breqtrd
    @0
    @1
    cA
    c1
    cexp
    co
    cA
    cle
    @0
    cA
    c1
    c3
    @16
    c1
    cn0
    wcel
    @0
    1nn0
    a1i
    c3
    c1
    cuz
    cfv
    wcel
    #
    @0
    @29
    @23
    c1
    c3
    cle
    wbr
    3z
    1le3
    c1
    c3
    1z
    eluz1i
    mpbir2an
    a1i
    @0
    @11
    cc0
    cA
    cle
    wbr
    #
    @0
    @10
    @11
    @12
    @15
    simp2bi
    @0
    cc0
    cr
    wcel
    #
    @10
    @11
    @30
    wi
    0re
    @16
    cc0
    cA
    ltle
    sylancr
    mpd
    @0
    @10
    @11
    @12
    @15
    simp3bi
    leexp2rd
    @0
    cA
    @0
    cA
    @16
    recnd
    exp1d
    breqtrd
    ltletrd
    @0
    @2
    cA
    @19
    @16
    posdifd
    mpbid
    @0
    @6
    @5
    cA
    clt
    wbr
    cA
    sin01bnd
    simpld
    @0
    @3
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @4
    @6
    wa
    @7
    wi
    #
    @0
    cA
    @2
    @16
    @19
    resubcld
    @0
    cA
    @16
    resincld
    @31
    @32
    @33
    @34
    0re
    cc0
    @3
    @5
    lttr
    mp3an1
    syl2anc
    mp2and
end
