include "c1.mm"
include "cneg.mm"
include "cpr.mm"
include "wcel.mm"
include "cc0.mm"
include "ctp.mm"
include "wa.mm"
include "co.mm"
include "wne.mm"
include "wceq.mm"
include "cif.mm"
include "cmul.mm"
include "clt.mm"
include "wbr.mm"
include "csn.mm"
include "cun.mm"
include "df-pr.mm"
include "snsstp1.mm"
include "snsstp3.mm"
include "unssi.mm"
include "eqsstri.mm"
include "sseli.mm"
include "signspval.mm"
include "sylan.mm"
include "neeq1d.mm"
include "wb.mm"
include "neeq1.mm"
include "bibi1d.mm"
include "wn.mm"
include "neirr.mm"
include "a1i.mm"
include "0re.mm"
include "ltnri.mm"
include "simpr.mm"
include "oveq2d.mm"
include "cc.mm"
include "wss.mm"
include "neg1cn.mm"
include "ax-1cn.mm"
include "prssi.mm"
include "mp2an.mm"
include "simpll.mm"
include "sseldi.mm"
include "mul01d.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "mtbiri.mm"
include "2falsed.mm"
include "simplr.mm"
include "tpcomb.mm"
include "syl6eleq.mm"
include "neqned.mm"
include "jca.mm"
include "cdif.mm"
include "eldifsn.mm"
include "neg1ne0.mm"
include "ax-1ne0.mm"
include "diftpsn3.mm"
include "eleq2i.mm"
include "bitr3i.mm"
include "sylib.mm"
include "cle.mm"
include "0le1.mm"
include "1re.mm"
include "lenlti.mm"
include "mpbi.mm"
include "neg1mulneg1e1.mm"
include "breq1i.mm"
include "mtbir.mm"
include "2false.mm"
include "oveq2.mm"
include "bibi12d.mm"
include "mpbiri.mm"
include "adantl.mm"
include "neg1rr.mm"
include "neg1lt0.mm"
include "0lt1.mm"
include "lttri.mm"
include "gtneii.mm"
include "mulid1i.mm"
include "eqbrtri.mm"
include "2th.mm"
include "elpri.mm"
include "mpjaodan.mm"
include "adantr.mm"
include "neeq2.mm"
include "oveq1.mm"
include "mpbird.mm"
include "necomi.mm"
include "mulcomi.mm"
include "wo.mm"
include "ad2antrr.mm"
include "ifbothda.mm"
include "bitrd.mm"

theorem signswch
  let c.pd: class .+^
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  assume signsw.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsw.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }

  disjoint a b
  disjoint X a
  disjoint X b
  disjoint Y a
  disjoint Y b
  assert |- ( ( X e. { -u 1 , 1 } /\ Y e. { -u 1 , 0 , 1 } ) -> ( ( X .+^ Y ) =/= X <-> ( X x. Y ) < 0 ) )

  proof
    cX
    c1
    cneg
    #
    c1
    cpr
    #
    wcel
    #
    cY
    @0
    cc0
    c1
    ctp
    #
    wcel
    #
    wa
    #
    cX
    cY
    c.pd
    co
    #
    cX
    wne
    cY
    cc0
    wceq
    #
    cX
    cY
    cif
    #
    cX
    wne
    #
    cX
    cY
    cmul
    co
    #
    cc0
    clt
    wbr
    #
    @5
    @6
    @8
    cX
    @2
    cX
    @3
    wcel
    @4
    @6
    @8
    wceq
    @1
    @3
    cX
    @1
    @0
    csn
    #
    c1
    csn
    #
    cun
    @3
    @0
    c1
    df-pr
    @12
    @13
    @3
    @0
    cc0
    c1
    snsstp1
    @0
    cc0
    c1
    snsstp3
    unssi
    eqsstri
    sseli
    c.pd
    cX
    cY
    va
    vb
    signsw.p
    signspval
    sylan
    neeq1d
    @7
    cX
    cX
    wne
    #
    @11
    wb
    cY
    cX
    wne
    #
    @11
    wb
    #
    @9
    @11
    wb
    @5
    cX
    cY
    cX
    @8
    wceq
    @14
    @9
    @11
    cX
    @8
    cX
    neeq1
    bibi1d
    cY
    @8
    wceq
    @15
    @9
    @11
    cY
    @8
    cX
    neeq1
    bibi1d
    @5
    @7
    wa
    #
    @14
    @11
    @14
    wn
    @17
    cX
    neirr
    a1i
    @17
    @11
    cc0
    cc0
    clt
    wbr
    cc0
    0re
    ltnri
    @17
    @10
    cc0
    cc0
    clt
    @17
    @10
    cX
    cc0
    cmul
    co
    cc0
    @17
    cY
    cc0
    cX
    cmul
    @5
    @7
    simpr
    oveq2d
    @17
    cX
    @17
    @1
    cc
    cX
    @0
    cc
    wcel
    c1
    cc
    wcel
    @1
    cc
    wss
    neg1cn
    ax-1cn
    @0
    c1
    cc
    prssi
    mp2an
    @2
    @4
    @7
    simpll
    sseldi
    mul01d
    eqtrd
    breq1d
    mtbiri
    2falsed
    @5
    @7
    wn
    #
    wa
    #
    cX
    @0
    wceq
    #
    @16
    cX
    c1
    wceq
    #
    @19
    cY
    @1
    wcel
    #
    @20
    @16
    @19
    cY
    @0
    c1
    cc0
    ctp
    #
    wcel
    #
    cY
    cc0
    wne
    #
    wa
    #
    @22
    @19
    @24
    @25
    @19
    cY
    @3
    @23
    @2
    @4
    @18
    simplr
    @0
    cc0
    c1
    tpcomb
    syl6eleq
    @19
    cY
    cc0
    @5
    @18
    simpr
    neqned
    jca
    @26
    cY
    @23
    cc0
    csn
    cdif
    #
    wcel
    @22
    cY
    @23
    cc0
    eldifsn
    @27
    @1
    cY
    @0
    cc0
    wne
    c1
    cc0
    wne
    @27
    @1
    wceq
    neg1ne0
    ax-1ne0
    @0
    c1
    cc0
    diftpsn3
    mp2an
    eleq2i
    bitr3i
    sylib
    #
    @22
    @20
    wa
    @16
    cY
    @0
    wne
    #
    @0
    cY
    cmul
    co
    #
    cc0
    clt
    wbr
    #
    wb
    #
    @22
    @32
    @20
    @22
    cY
    @0
    wceq
    #
    @32
    cY
    c1
    wceq
    #
    @33
    @32
    @22
    @33
    @32
    @0
    @0
    wne
    #
    @0
    @0
    cmul
    co
    #
    cc0
    clt
    wbr
    #
    wb
    @35
    @37
    @0
    neirr
    @37
    c1
    cc0
    clt
    wbr
    #
    cc0
    c1
    cle
    wbr
    @38
    wn
    0le1
    cc0
    c1
    0re
    1re
    lenlti
    mpbi
    #
    @36
    c1
    cc0
    clt
    neg1mulneg1e1
    breq1i
    mtbir
    2false
    @33
    @29
    @35
    @31
    @37
    cY
    @0
    @0
    neeq1
    @33
    @30
    @36
    cc0
    clt
    cY
    @0
    @0
    cmul
    oveq2
    breq1d
    bibi12d
    mpbiri
    adantl
    @34
    @32
    @22
    @34
    @32
    c1
    @0
    wne
    #
    @0
    c1
    cmul
    co
    #
    cc0
    clt
    wbr
    #
    wb
    @40
    @42
    @0
    c1
    neg1rr
    @0
    cc0
    clt
    wbr
    cc0
    c1
    clt
    wbr
    @0
    c1
    clt
    wbr
    neg1lt0
    0lt1
    @0
    cc0
    c1
    neg1rr
    0re
    1re
    lttri
    mp2an
    gtneii
    #
    @41
    @0
    cc0
    clt
    @0
    neg1cn
    mulid1i
    neg1lt0
    eqbrtri
    #
    2th
    @34
    @29
    @40
    @31
    @42
    cY
    c1
    @0
    neeq1
    @34
    @30
    @41
    cc0
    clt
    cY
    c1
    @0
    cmul
    oveq2
    breq1d
    bibi12d
    mpbiri
    adantl
    cY
    @0
    c1
    elpri
    #
    mpjaodan
    adantr
    @20
    @16
    @32
    wb
    @22
    @20
    @15
    @29
    @11
    @31
    cX
    @0
    cY
    neeq2
    @20
    @10
    @30
    cc0
    clt
    cX
    @0
    cY
    cmul
    oveq1
    breq1d
    bibi12d
    adantl
    mpbird
    sylan
    @19
    @22
    @21
    @16
    @28
    @22
    @21
    wa
    @16
    cY
    c1
    wne
    #
    c1
    cY
    cmul
    co
    #
    cc0
    clt
    wbr
    #
    wb
    #
    @22
    @49
    @21
    @22
    @33
    @49
    @34
    @33
    @49
    @22
    @33
    @49
    @0
    c1
    wne
    #
    c1
    @0
    cmul
    co
    #
    cc0
    clt
    wbr
    #
    wb
    @50
    @52
    c1
    @0
    @43
    necomi
    @42
    @52
    @44
    @41
    @51
    cc0
    clt
    @0
    c1
    neg1cn
    ax-1cn
    mulcomi
    breq1i
    mpbi
    2th
    @33
    @46
    @50
    @48
    @52
    cY
    @0
    c1
    neeq1
    @33
    @47
    @51
    cc0
    clt
    cY
    @0
    c1
    cmul
    oveq2
    breq1d
    bibi12d
    mpbiri
    adantl
    @34
    @49
    @22
    @34
    @49
    c1
    c1
    wne
    #
    c1
    c1
    cmul
    co
    #
    cc0
    clt
    wbr
    #
    wb
    @53
    @55
    c1
    neirr
    @55
    @38
    @39
    @54
    c1
    cc0
    clt
    c1
    ax-1cn
    mulid1i
    breq1i
    mtbir
    2false
    @34
    @46
    @53
    @48
    @55
    cY
    c1
    c1
    neeq1
    @34
    @47
    @54
    cc0
    clt
    cY
    c1
    c1
    cmul
    oveq2
    breq1d
    bibi12d
    mpbiri
    adantl
    @45
    mpjaodan
    adantr
    @21
    @16
    @49
    wb
    @22
    @21
    @15
    @46
    @11
    @48
    cX
    c1
    cY
    neeq2
    @21
    @10
    @47
    cc0
    clt
    cX
    c1
    cY
    cmul
    oveq1
    breq1d
    bibi12d
    adantl
    mpbird
    sylan
    @2
    @20
    @21
    wo
    @4
    @18
    cX
    @0
    c1
    elpri
    ad2antrr
    mpjaodan
    ifbothda
    bitrd
end
