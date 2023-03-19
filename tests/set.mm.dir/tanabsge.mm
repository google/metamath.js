include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cioo.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "ctan.mm"
include "cle.mm"
include "wceq.mm"
include "wa.mm"
include "cr.mm"
include "elioore.mm"
include "adantr.mm"
include "renegcld.mm"
include "ccos.mm"
include "csin.mm"
include "lt0neg1d.mm"
include "biimpa.mm"
include "eliooord.mm"
include "simpld.mm"
include "wb.mm"
include "halfpire.mm"
include "ltnegcon1.mm"
include "sylancr.mm"
include "mpbid.mm"
include "cxr.mm"
include "w3a.mm"
include "0xr.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "sincosq1sgn.mm"
include "syl.mm"
include "simprd.mm"
include "gt0ne0d.mm"
include "retancld.mm"
include "tangtx.mm"
include "ltled.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "sylancl.mm"
include "imp.mm"
include "absnidd.mm"
include "cc.mm"
include "recnd.mm"
include "negnegd.mm"
include "fveq2d.mm"
include "wne.mm"
include "negcld.mm"
include "tanneg.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "absnegd.mm"
include "0red.mm"
include "mpd.mm"
include "letrd.mm"
include "absidd.mm"
include "3eqtrd.mm"
include "3brtr4d.mm"
include "abs0.mm"
include "eqeltri.mm"
include "leidi.mm"
include "a1i.mm"
include "simpr.mm"
include "tan0.mm"
include "syl6eq.mm"
include "w3o.mm"
include "lttri4.mm"
include "mpjao3dan.mm"

theorem tanabsge
  let cA: class A


  assert |- ( A e. ( -u ( _pi / 2 ) (,) ( _pi / 2 ) ) -> ( abs ` A ) <_ ( abs ` ( tan ` A ) ) )

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
    cA
    cc0
    clt
    wbr
    #
    cA
    cabs
    cfv
    #
    cA
    ctan
    cfv
    #
    cabs
    cfv
    #
    cle
    wbr
    cA
    cc0
    wceq
    #
    cc0
    cA
    clt
    wbr
    #
    @2
    @3
    wa
    #
    cA
    cneg
    #
    @10
    ctan
    cfv
    #
    @4
    @6
    cle
    @9
    @10
    @11
    @9
    cA
    @2
    cA
    cr
    wcel
    #
    @3
    cA
    @1
    @0
    elioore
    #
    adantr
    #
    renegcld
    #
    @9
    @10
    @15
    @9
    @10
    ccos
    cfv
    #
    @9
    cc0
    @10
    csin
    cfv
    clt
    wbr
    #
    cc0
    @16
    clt
    wbr
    #
    @9
    @10
    cc0
    @0
    cioo
    co
    #
    wcel
    #
    @17
    @18
    wa
    @9
    @10
    cr
    wcel
    #
    cc0
    @10
    clt
    wbr
    #
    @10
    @0
    clt
    wbr
    #
    @20
    @15
    @2
    @3
    @22
    @2
    cA
    @13
    lt0neg1d
    biimpa
    #
    @9
    @1
    cA
    clt
    wbr
    #
    @23
    @2
    @25
    @3
    @2
    @25
    cA
    @0
    clt
    wbr
    #
    cA
    @1
    @0
    eliooord
    #
    simpld
    adantr
    @9
    @0
    cr
    wcel
    @12
    @25
    @23
    wb
    halfpire
    @14
    @0
    cA
    ltnegcon1
    sylancr
    mpbid
    cc0
    cxr
    wcel
    #
    @0
    cxr
    wcel
    #
    @20
    @21
    @22
    @23
    w3a
    wb
    0xr
    @0
    halfpire
    rexri
    #
    cc0
    @0
    @10
    elioo2
    mp2an
    syl3anbrc
    #
    @10
    sincosq1sgn
    syl
    simprd
    gt0ne0d
    #
    retancld
    #
    @9
    @20
    @10
    @11
    clt
    wbr
    @31
    @10
    tangtx
    syl
    ltled
    #
    @9
    cA
    @14
    @2
    @3
    cA
    cc0
    cle
    wbr
    #
    @2
    @12
    cc0
    cr
    wcel
    #
    @3
    @35
    wi
    @13
    0re
    cA
    cc0
    ltle
    sylancl
    imp
    absnidd
    @9
    @6
    @11
    cneg
    #
    cabs
    cfv
    @11
    cabs
    cfv
    @11
    @9
    @5
    @37
    cabs
    @9
    @10
    cneg
    #
    ctan
    cfv
    #
    @5
    @37
    @9
    @38
    cA
    ctan
    @9
    cA
    @2
    cA
    cc
    wcel
    @3
    @2
    cA
    @13
    recnd
    adantr
    #
    negnegd
    fveq2d
    @9
    @10
    cc
    wcel
    @16
    cc0
    wne
    @39
    @37
    wceq
    @9
    cA
    @40
    negcld
    @32
    @10
    tanneg
    syl2anc
    eqtr3d
    fveq2d
    @9
    @11
    @9
    @11
    @33
    recnd
    absnegd
    @9
    @11
    @33
    @9
    cc0
    @10
    @11
    @9
    0red
    @15
    @33
    @9
    @22
    cc0
    @10
    cle
    wbr
    #
    @24
    @9
    @36
    @21
    @22
    @41
    wi
    0re
    @15
    cc0
    @10
    ltle
    sylancr
    mpd
    @34
    letrd
    absidd
    3eqtrd
    3brtr4d
    @2
    @7
    wa
    #
    cc0
    cabs
    cfv
    #
    @43
    @4
    @6
    cle
    @43
    @43
    cle
    wbr
    @42
    @43
    @43
    cc0
    cr
    abs0
    0re
    eqeltri
    leidi
    a1i
    @42
    cA
    cc0
    cabs
    @2
    @7
    simpr
    #
    fveq2d
    @42
    @5
    cc0
    cabs
    @42
    @5
    cc0
    ctan
    cfv
    cc0
    @42
    cA
    cc0
    ctan
    @44
    fveq2d
    tan0
    syl6eq
    fveq2d
    3brtr4d
    @2
    @8
    wa
    #
    cA
    @5
    @4
    @6
    cle
    @45
    cA
    @5
    @2
    @12
    @8
    @13
    adantr
    #
    @45
    cA
    @46
    @45
    cA
    ccos
    cfv
    #
    @45
    cc0
    cA
    csin
    cfv
    clt
    wbr
    #
    cc0
    @47
    clt
    wbr
    #
    @45
    cA
    @19
    wcel
    #
    @48
    @49
    wa
    @45
    @12
    @8
    @26
    @50
    @46
    @2
    @8
    simpr
    @2
    @26
    @8
    @2
    @25
    @26
    @27
    simprd
    adantr
    @28
    @29
    @50
    @12
    @8
    @26
    w3a
    wb
    0xr
    @30
    cc0
    @0
    cA
    elioo2
    mp2an
    syl3anbrc
    #
    cA
    sincosq1sgn
    syl
    simprd
    gt0ne0d
    retancld
    #
    @45
    @50
    cA
    @5
    clt
    wbr
    @51
    cA
    tangtx
    syl
    ltled
    #
    @45
    cA
    @46
    @2
    @8
    cc0
    cA
    cle
    wbr
    #
    @2
    @36
    @12
    @8
    @54
    wi
    0re
    @13
    cc0
    cA
    ltle
    sylancr
    imp
    #
    absidd
    @45
    @5
    @52
    @45
    cc0
    cA
    @5
    @45
    0red
    @46
    @52
    @55
    @53
    letrd
    absidd
    3brtr4d
    @2
    @12
    @36
    @3
    @7
    @8
    w3o
    @13
    0re
    cA
    cc0
    lttri4
    sylancl
    mpjao3dan
end
