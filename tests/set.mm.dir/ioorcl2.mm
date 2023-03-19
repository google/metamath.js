include "cioo.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "covol.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wex.mm"
include "wi.mm"
include "n0.mm"
include "c1.mm"
include "caddc.mm"
include "cmin.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "elioore.mm"
include "adantr.mm"
include "peano2re.mm"
include "adantl.mm"
include "resubcld.mm"
include "rexrd.mm"
include "eliooxr.mm"
include "simpld.mm"
include "ltp1.mm"
include "cle.mm"
include "wn.mm"
include "wceq.mm"
include "cc0.mm"
include "0red.mm"
include "simpr.mm"
include "wss.mm"
include "ioossre.mm"
include "ovolge0.mm"
include "mp1i.mm"
include "lep1.mm"
include "letrd.mm"
include "subge02d.mm"
include "mpbid.mm"
include "ovolioo.mm"
include "syl3anc.mm"
include "recnd.mm"
include "nncand.mm"
include "eqtrd.mm"
include "iooss1.mm"
include "sylan.mm"
include "simprd.mm"
include "eliooord.mm"
include "xrltle.mm"
include "syl2anc.mm"
include "mpd.mm"
include "iooss2.mm"
include "sstrd.mm"
include "ovolss.mm"
include "sylancl.mm"
include "eqbrtrrd.mm"
include "ex.mm"
include "wb.mm"
include "xrlenlt.mm"
include "lenltd.mm"
include "3imtr3d.mm"
include "mt4d.mm"
include "xrre2.mm"
include "syl32anc.mm"
include "readdcld.mm"
include "addge01d.mm"
include "pncan2d.mm"
include "jca.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "imp.mm"

theorem ioorcl2
  let cA: class A
  let cB: class B
  let vz: setvar z


  assert |- ( ( ( A (,) B ) =/= (/) /\ ( vol* ` ( A (,) B ) ) e. RR ) -> ( A e. RR /\ B e. RR ) )

  proof
    cA
    cB
    cioo
    co
    #
    c0
    wne
    #
    @0
    covol
    cfv
    #
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    @1
    vz
    cv
    #
    @0
    wcel
    #
    vz
    wex
    @3
    @6
    wi
    #
    vz
    @0
    n0
    @8
    @9
    vz
    @8
    @3
    @6
    @8
    @3
    wa
    #
    @4
    @5
    @10
    @7
    @2
    c1
    caddc
    co
    #
    cmin
    co
    #
    cxr
    wcel
    #
    cA
    cxr
    wcel
    #
    @7
    cxr
    wcel
    #
    @12
    cA
    clt
    wbr
    #
    cA
    @7
    clt
    wbr
    #
    @4
    @10
    @12
    @10
    @7
    @11
    @8
    @7
    cr
    wcel
    #
    @3
    @7
    cA
    cB
    elioore
    adantr
    #
    @3
    @11
    cr
    wcel
    @8
    @2
    peano2re
    adantl
    #
    resubcld
    #
    rexrd
    #
    @10
    @14
    cB
    cxr
    wcel
    #
    @8
    @14
    @23
    wa
    @3
    @7
    cA
    cB
    eliooxr
    adantr
    #
    simpld
    #
    @10
    @7
    @19
    rexrd
    #
    @10
    @2
    @11
    clt
    wbr
    #
    @16
    @3
    @27
    @8
    @2
    ltp1
    adantl
    #
    @10
    cA
    @12
    cle
    wbr
    #
    @11
    @2
    cle
    wbr
    #
    @16
    wn
    #
    @27
    wn
    #
    @10
    @29
    @30
    @10
    @29
    wa
    #
    @12
    @7
    cioo
    co
    #
    covol
    cfv
    #
    @11
    @2
    cle
    @10
    @35
    @11
    wceq
    @29
    @10
    @35
    @7
    @12
    cmin
    co
    #
    @11
    @10
    @12
    cr
    wcel
    @18
    @12
    @7
    cle
    wbr
    #
    @35
    @36
    wceq
    @21
    @19
    @10
    cc0
    @11
    cle
    wbr
    #
    @37
    @10
    cc0
    @2
    @11
    @10
    0red
    @8
    @3
    simpr
    #
    @20
    @0
    cr
    wss
    #
    cc0
    @2
    cle
    wbr
    @10
    cA
    cB
    ioossre
    #
    @0
    ovolge0
    mp1i
    @3
    @2
    @11
    cle
    wbr
    @8
    @2
    lep1
    adantl
    letrd
    #
    @10
    @7
    @11
    @19
    @20
    subge02d
    mpbid
    @12
    @7
    ovolioo
    syl3anc
    @10
    @7
    @11
    @10
    @7
    @19
    recnd
    #
    @10
    @11
    @20
    recnd
    #
    nncand
    eqtrd
    adantr
    @33
    @34
    @0
    wss
    @40
    @35
    @2
    cle
    wbr
    @33
    @34
    cA
    @7
    cioo
    co
    #
    @0
    @10
    @14
    @29
    @34
    @45
    wss
    @25
    cA
    @12
    @7
    iooss1
    sylan
    @10
    @45
    @0
    wss
    #
    @29
    @10
    @23
    @7
    cB
    cle
    wbr
    #
    @46
    @10
    @14
    @23
    @24
    simprd
    #
    @10
    @7
    cB
    clt
    wbr
    #
    @47
    @10
    @17
    @49
    @8
    @17
    @49
    wa
    @3
    @7
    cA
    cB
    eliooord
    adantr
    #
    simprd
    #
    @10
    @15
    @23
    @49
    @47
    wi
    @26
    @48
    @7
    cB
    xrltle
    syl2anc
    mpd
    cA
    @7
    cB
    iooss2
    syl2anc
    adantr
    sstrd
    @41
    @34
    @0
    ovolss
    sylancl
    eqbrtrrd
    ex
    @10
    @14
    @13
    @29
    @31
    wb
    @25
    @22
    cA
    @12
    xrlenlt
    syl2anc
    @10
    @11
    @2
    @20
    @39
    lenltd
    #
    3imtr3d
    mt4d
    @10
    @17
    @49
    @50
    simpld
    #
    @12
    cA
    @7
    xrre2
    syl32anc
    @10
    @15
    @23
    @7
    @11
    caddc
    co
    #
    cxr
    wcel
    #
    @49
    cB
    @54
    clt
    wbr
    #
    @5
    @26
    @48
    @10
    @54
    @10
    @7
    @11
    @19
    @20
    readdcld
    #
    rexrd
    #
    @51
    @10
    @27
    @56
    @28
    @10
    @54
    cB
    cle
    wbr
    #
    @30
    @56
    wn
    #
    @32
    @10
    @59
    @30
    @10
    @59
    wa
    #
    @7
    @54
    cioo
    co
    #
    covol
    cfv
    #
    @11
    @2
    cle
    @10
    @63
    @11
    wceq
    @59
    @10
    @63
    @54
    @7
    cmin
    co
    #
    @11
    @10
    @18
    @54
    cr
    wcel
    @7
    @54
    cle
    wbr
    #
    @63
    @64
    wceq
    @19
    @57
    @10
    @38
    @65
    @42
    @10
    @7
    @11
    @19
    @20
    addge01d
    mpbid
    @7
    @54
    ovolioo
    syl3anc
    @10
    @7
    @11
    @43
    @44
    pncan2d
    eqtrd
    adantr
    @61
    @62
    @0
    wss
    @40
    @63
    @2
    cle
    wbr
    @61
    @62
    @7
    cB
    cioo
    co
    #
    @0
    @10
    @23
    @59
    @62
    @66
    wss
    @48
    @7
    @54
    cB
    iooss2
    sylan
    @10
    @66
    @0
    wss
    #
    @59
    @10
    @14
    cA
    @7
    cle
    wbr
    #
    @67
    @25
    @10
    @17
    @68
    @53
    @10
    @14
    @15
    @17
    @68
    wi
    @25
    @26
    cA
    @7
    xrltle
    syl2anc
    mpd
    cA
    @7
    cB
    iooss1
    syl2anc
    adantr
    sstrd
    @41
    @62
    @0
    ovolss
    sylancl
    eqbrtrrd
    ex
    @10
    @55
    @23
    @59
    @60
    wb
    @58
    @48
    @54
    cB
    xrlenlt
    syl2anc
    @52
    3imtr3d
    mt4d
    @7
    cB
    @54
    xrre2
    syl32anc
    jca
    ex
    exlimiv
    sylbi
    imp
end
