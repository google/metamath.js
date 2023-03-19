include "cabl.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cgcd.mm"
include "cmul.mm"
include "cdvds.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cz.mm"
include "cn0.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "grpcl.mm"
include "syl3an1.mm"
include "odcl.mm"
include "syl.mm"
include "nn0zd.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "gcdcld.mm"
include "zmulcld.mm"
include "adantr.mm"
include "dvds0.mm"
include "wb.mm"
include "gcdeq0.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "oveq12.mm"
include "0cn.mm"
include "mul01i.mm"
include "syl6eq.mm"
include "breqtrrd.mm"
include "wne.mm"
include "cdiv.mm"
include "cmg.mm"
include "c0g.mm"
include "simpl1.mm"
include "gcddvds.mm"
include "simpld.mm"
include "wi.mm"
include "dvdsmultr1.mm"
include "syl3anc.mm"
include "mpd.mm"
include "simpr.mm"
include "dvdsval2.mm"
include "mpbid.mm"
include "simpl2.mm"
include "simpl3.mm"
include "eqid.mm"
include "mulgdi.mm"
include "syl13anc.mm"
include "simprd.mm"
include "dvdsmul1.mm"
include "zcnd.mm"
include "divassd.mm"
include "oddvds.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "grpidcl.mm"
include "grplid.mm"
include "mpbird.mm"
include "dvdsmulcr.mm"
include "syl112anc.mm"
include "divcan1d.mm"
include "breqtrd.mm"
include "pm2.61dane.mm"

theorem odadd1
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cO: class O
  let cX: class X
  assume odadd1.1: |- O = ( od ` G )
  assume odadd1.2: |- X = ( Base ` G )
  assume odadd1.3: |- .+ = ( +g ` G )


  assert |- ( ( G e. Abel /\ A e. X /\ B e. X ) -> ( ( O ` ( A .+ B ) ) x. ( ( O ` A ) gcd ( O ` B ) ) ) || ( ( O ` A ) x. ( O ` B ) ) )

  proof
    cG
    cabl
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    c.pl
    co
    #
    cO
    cfv
    #
    cA
    cO
    cfv
    #
    cB
    cO
    cfv
    #
    cgcd
    co
    #
    cmul
    co
    #
    @6
    @7
    cmul
    co
    #
    cdvds
    wbr
    @8
    cc0
    @3
    @8
    cc0
    wceq
    #
    wa
    #
    @9
    cc0
    @10
    cdvds
    @12
    @9
    cz
    wcel
    #
    @9
    cc0
    cdvds
    wbr
    @3
    @13
    @11
    @3
    @5
    @8
    @3
    @5
    @3
    @4
    cX
    wcel
    #
    @5
    cn0
    wcel
    @0
    cG
    cgrp
    wcel
    #
    @1
    @2
    @14
    cG
    ablgrp
    #
    cX
    c.pl
    cG
    cA
    cB
    odadd1.2
    odadd1.3
    grpcl
    syl3an1
    #
    @4
    cG
    cO
    cX
    odadd1.2
    odadd1.1
    odcl
    syl
    nn0zd
    #
    @3
    @8
    @3
    @6
    @7
    @3
    @6
    @1
    @0
    @6
    cn0
    wcel
    @2
    cA
    cG
    cO
    cX
    odadd1.2
    odadd1.1
    odcl
    3ad2ant2
    nn0zd
    #
    @3
    @7
    @2
    @0
    @7
    cn0
    wcel
    @1
    cB
    cG
    cO
    cX
    odadd1.2
    odadd1.1
    odcl
    3ad2ant3
    nn0zd
    #
    gcdcld
    nn0zd
    #
    zmulcld
    adantr
    @9
    dvds0
    syl
    @12
    @6
    cc0
    wceq
    @7
    cc0
    wceq
    wa
    #
    @10
    cc0
    wceq
    @3
    @11
    @22
    @3
    @6
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    @11
    @22
    wb
    @19
    @20
    @6
    @7
    gcdeq0
    syl2anc
    biimpa
    @22
    @10
    cc0
    cc0
    cmul
    co
    cc0
    @6
    cc0
    @7
    cc0
    cmul
    oveq12
    cc0
    0cn
    mul01i
    syl6eq
    syl
    breqtrrd
    @3
    @8
    cc0
    wne
    #
    wa
    #
    @9
    @10
    @8
    cdiv
    co
    #
    @8
    cmul
    co
    #
    @10
    cdvds
    @26
    @9
    @28
    cdvds
    wbr
    #
    @5
    @27
    cdvds
    wbr
    #
    @26
    @30
    @27
    @4
    cG
    cmg
    cfv
    #
    co
    #
    cG
    c0g
    cfv
    #
    wceq
    #
    @26
    @32
    @27
    cA
    @31
    co
    #
    @27
    cB
    @31
    co
    #
    c.pl
    co
    #
    @33
    @26
    @0
    @27
    cz
    wcel
    #
    @1
    @2
    @32
    @37
    wceq
    @0
    @1
    @2
    @25
    simpl1
    #
    @26
    @8
    @10
    cdvds
    wbr
    #
    @38
    @26
    @8
    @6
    cdvds
    wbr
    #
    @40
    @26
    @41
    @8
    @7
    cdvds
    wbr
    #
    @26
    @23
    @24
    @41
    @42
    wa
    @3
    @23
    @25
    @19
    adantr
    #
    @3
    @24
    @25
    @20
    adantr
    #
    @6
    @7
    gcddvds
    syl2anc
    #
    simpld
    #
    @26
    @8
    cz
    wcel
    #
    @23
    @24
    @41
    @40
    wi
    @3
    @47
    @25
    @21
    adantr
    #
    @43
    @44
    @8
    @6
    @7
    dvdsmultr1
    syl3anc
    mpd
    @26
    @47
    @25
    @10
    cz
    wcel
    @40
    @38
    wb
    @48
    @3
    @25
    simpr
    #
    @26
    @6
    @7
    @43
    @44
    zmulcld
    #
    @8
    @10
    dvdsval2
    syl3anc
    mpbid
    #
    @0
    @1
    @2
    @25
    simpl2
    #
    @0
    @1
    @2
    @25
    simpl3
    #
    cX
    c.pl
    @31
    cG
    @27
    cA
    cB
    odadd1.2
    @31
    eqid
    #
    odadd1.3
    mulgdi
    syl13anc
    @26
    @37
    @33
    @33
    c.pl
    co
    #
    @33
    @26
    @35
    @33
    @36
    @33
    c.pl
    @26
    @6
    @27
    cdvds
    wbr
    #
    @35
    @33
    wceq
    #
    @26
    @6
    @6
    @7
    @8
    cdiv
    co
    #
    cmul
    co
    #
    @27
    cdvds
    @26
    @23
    @58
    cz
    wcel
    #
    @6
    @59
    cdvds
    wbr
    @43
    @26
    @42
    @60
    @26
    @41
    @42
    @45
    simprd
    @26
    @47
    @25
    @24
    @42
    @60
    wb
    @48
    @49
    @44
    @8
    @7
    dvdsval2
    syl3anc
    mpbid
    @6
    @58
    dvdsmul1
    syl2anc
    @26
    @6
    @7
    @8
    @26
    @6
    @43
    zcnd
    #
    @26
    @7
    @44
    zcnd
    #
    @26
    @8
    @48
    zcnd
    #
    @49
    divassd
    breqtrrd
    @26
    @15
    @1
    @38
    @56
    @57
    wb
    @26
    @0
    @15
    @39
    @16
    syl
    #
    @52
    @51
    cA
    @31
    cG
    @27
    cO
    cX
    @33
    odadd1.2
    odadd1.1
    @54
    @33
    eqid
    #
    oddvds
    syl3anc
    mpbid
    @26
    @7
    @27
    cdvds
    wbr
    #
    @36
    @33
    wceq
    #
    @26
    @7
    @7
    @6
    @8
    cdiv
    co
    #
    cmul
    co
    #
    @27
    cdvds
    @26
    @24
    @68
    cz
    wcel
    #
    @7
    @69
    cdvds
    wbr
    @44
    @26
    @41
    @70
    @46
    @26
    @47
    @25
    @23
    @41
    @70
    wb
    @48
    @49
    @43
    @8
    @6
    dvdsval2
    syl3anc
    mpbid
    @7
    @68
    dvdsmul1
    syl2anc
    @26
    @27
    @7
    @6
    cmul
    co
    #
    @8
    cdiv
    co
    @69
    @26
    @10
    @71
    @8
    cdiv
    @26
    @6
    @7
    @61
    @62
    mulcomd
    oveq1d
    @26
    @7
    @6
    @8
    @62
    @61
    @63
    @49
    divassd
    eqtrd
    breqtrrd
    @26
    @15
    @2
    @38
    @66
    @67
    wb
    @64
    @53
    @51
    cB
    @31
    cG
    @27
    cO
    cX
    @33
    odadd1.2
    odadd1.1
    @54
    @65
    oddvds
    syl3anc
    mpbid
    oveq12d
    @26
    @15
    @33
    cX
    wcel
    #
    @55
    @33
    wceq
    @64
    @26
    @15
    @72
    @64
    cX
    cG
    @33
    odadd1.2
    @65
    grpidcl
    syl
    cX
    c.pl
    cG
    @33
    @33
    odadd1.2
    odadd1.3
    @65
    grplid
    syl2anc
    eqtrd
    eqtrd
    @26
    @15
    @14
    @38
    @30
    @34
    wb
    @64
    @3
    @14
    @25
    @17
    adantr
    @51
    @4
    @31
    cG
    @27
    cO
    cX
    @33
    odadd1.2
    odadd1.1
    @54
    @65
    oddvds
    syl3anc
    mpbird
    @26
    @5
    cz
    wcel
    #
    @38
    @47
    @25
    @29
    @30
    wb
    @3
    @73
    @25
    @18
    adantr
    @51
    @48
    @49
    @8
    @5
    @27
    dvdsmulcr
    syl112anc
    mpbird
    @26
    @10
    @8
    @26
    @10
    @50
    zcnd
    @63
    @49
    divcan1d
    breqtrd
    pm2.61dane
end
