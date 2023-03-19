include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cxmt.mm"
include "cxr.mm"
include "wb.mm"
include "elbl.mm"
include "syl3anc.mm"
include "simprbda.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cxad.mm"
include "adantr.mm"
include "xmetcl.mm"
include "rexrd.mm"
include "xaddcld.mm"
include "ad2antrr.mm"
include "cle.mm"
include "xmettri2.mm"
include "syl13anc.mm"
include "simplbda.mm"
include "xltadd2.mm"
include "mpbid.mm"
include "xrlelttrd.mm"
include "cxne.mm"
include "xnegcld.mm"
include "xleadd1a.mm"
include "syl31anc.mm"
include "xnpcan.mm"
include "sylan.mm"
include "breqtrd.mm"
include "xrltletrd.mm"
include "cc0.mm"
include "cmnf.mm"
include "wne.mm"
include "0xr.mm"
include "a1i.mm"
include "xmetge0.mm"
include "xrletrd.mm"
include "ge0nemnf.mm"
include "syl2anc.mm"
include "wi.mm"
include "xaddmnf1.mm"
include "ex.mm"
include "syl.mm"
include "simpr.mm"
include "xnegeq.mm"
include "xnegpnf.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "sylibrd.mm"
include "necon1d.mm"
include "mpd.mm"
include "oveq12d.mm"
include "pnfaddmnf.mm"
include "biantrud.mm"
include "xrletri3.mm"
include "sylancl.mm"
include "xmeteq0.mm"
include "3bitr2d.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "3brtr3d.mm"
include "wo.mm"
include "xrltle.mm"
include "sylancr.mm"
include "jca.mm"
include "xrnemnf.mm"
include "sylib.mm"
include "mpjaodan.mm"
include "mpbir2and.mm"
include "ssrdv.mm"

theorem xblss2
  let wph: wff ph
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cX: class X
  let cA: class A
  let vx: setvar x
  let vr: setvar r
  let vy: setvar y
  assume xblss2.1: |- ( ph -> D e. ( *Met ` X ) )
  assume xblss2.2: |- ( ph -> P e. X )
  assume xblss2.3: |- ( ph -> Q e. X )
  assume xblss2.4: |- ( ph -> R e. RR* )
  assume xblss2.5: |- ( ph -> S e. RR* )
  assume xblss2.6: |- ( ph -> ( P D Q ) e. RR )
  assume xblss2.7: |- ( ph -> ( P D Q ) <_ ( S +e -e R ) )


  assert |- ( ph -> ( P ( ball ` D ) R ) C_ ( Q ( ball ` D ) S ) )

  proof
    wph
    vx
    cP
    cR
    cD
    cbl
    cfv
    #
    co
    #
    cQ
    cS
    @0
    co
    #
    wph
    vx
    cv
    #
    @1
    wcel
    #
    @3
    @2
    wcel
    #
    wph
    @4
    wa
    #
    @5
    @3
    cX
    wcel
    #
    cQ
    @3
    cD
    co
    #
    cS
    clt
    wbr
    #
    wph
    @4
    @7
    cP
    @3
    cD
    co
    #
    cR
    clt
    wbr
    #
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    cR
    cxr
    wcel
    #
    @4
    @7
    @11
    wa
    wb
    xblss2.1
    xblss2.2
    xblss2.4
    @3
    cD
    cP
    cR
    cX
    elbl
    syl3anc
    #
    simprbda
    #
    @6
    cR
    cr
    wcel
    #
    @9
    cR
    cpnf
    wceq
    #
    @6
    @17
    wa
    #
    @8
    cP
    cQ
    cD
    co
    #
    cR
    cxad
    co
    #
    cS
    @6
    @8
    cxr
    wcel
    #
    @17
    @6
    @12
    cQ
    cX
    wcel
    #
    @7
    @22
    wph
    @12
    @4
    xblss2.1
    adantr
    #
    wph
    @23
    @4
    xblss2.3
    adantr
    #
    @16
    cQ
    @3
    cD
    cX
    xmetcl
    syl3anc
    #
    adantr
    @6
    @21
    cxr
    wcel
    @17
    @6
    @20
    cR
    @6
    @20
    wph
    @20
    cr
    wcel
    #
    @4
    xblss2.6
    adantr
    #
    rexrd
    #
    wph
    @14
    @4
    xblss2.4
    adantr
    #
    xaddcld
    #
    adantr
    wph
    cS
    cxr
    wcel
    #
    @4
    @17
    xblss2.5
    ad2antrr
    @6
    @8
    @21
    clt
    wbr
    @17
    @6
    @8
    @20
    @10
    cxad
    co
    #
    @21
    @26
    @6
    @20
    @10
    @29
    @6
    @12
    @13
    @7
    @10
    cxr
    wcel
    #
    @24
    wph
    @13
    @4
    xblss2.2
    adantr
    #
    @16
    cP
    @3
    cD
    cX
    xmetcl
    syl3anc
    #
    xaddcld
    @31
    @6
    @12
    @13
    @23
    @7
    @8
    @33
    cle
    wbr
    @24
    @35
    @25
    @16
    cQ
    @3
    cP
    cD
    cX
    xmettri2
    syl13anc
    @6
    @11
    @33
    @21
    clt
    wbr
    #
    wph
    @4
    @7
    @11
    @15
    simplbda
    #
    @6
    @34
    @14
    @27
    @11
    @37
    wb
    @36
    @30
    @28
    @10
    cR
    @20
    xltadd2
    syl3anc
    mpbid
    xrlelttrd
    adantr
    @19
    @21
    cS
    cR
    cxne
    #
    cxad
    co
    #
    cR
    cxad
    co
    #
    cS
    cle
    @6
    @21
    @41
    cle
    wbr
    #
    @17
    @6
    @20
    cxr
    wcel
    #
    @40
    cxr
    wcel
    #
    @14
    @20
    @40
    cle
    wbr
    #
    @42
    @29
    @6
    cS
    @39
    wph
    @32
    @4
    xblss2.5
    adantr
    #
    @6
    cR
    @30
    xnegcld
    xaddcld
    #
    @30
    wph
    @45
    @4
    xblss2.7
    adantr
    #
    @20
    @40
    cR
    xleadd1a
    syl31anc
    adantr
    @6
    @32
    @17
    @41
    cS
    wceq
    @46
    cS
    cR
    xnpcan
    sylan
    breqtrd
    xrltletrd
    @6
    @18
    wa
    #
    @10
    cR
    @8
    cS
    clt
    @6
    @11
    @18
    @38
    adantr
    @49
    cP
    cQ
    @3
    cD
    @49
    @20
    cc0
    cle
    wbr
    #
    cP
    cQ
    wceq
    #
    @49
    @20
    @40
    cc0
    cle
    wph
    @45
    @4
    @18
    xblss2.7
    ad2antrr
    @49
    @40
    cpnf
    cmnf
    cxad
    co
    cc0
    @49
    cS
    cpnf
    @39
    cmnf
    cxad
    @49
    @40
    cmnf
    wne
    #
    cS
    cpnf
    wceq
    @6
    @52
    @18
    @6
    @44
    cc0
    @40
    cle
    wbr
    @52
    @47
    @6
    cc0
    @20
    @40
    cc0
    cxr
    wcel
    #
    @6
    0xr
    a1i
    #
    @29
    @47
    @6
    @12
    @13
    @23
    cc0
    @20
    cle
    wbr
    #
    @24
    @35
    @25
    cP
    cQ
    cD
    cX
    xmetge0
    syl3anc
    #
    @48
    xrletrd
    @40
    ge0nemnf
    syl2anc
    adantr
    @49
    cS
    cpnf
    @40
    cmnf
    @49
    cS
    cpnf
    wne
    #
    cS
    cmnf
    cxad
    co
    #
    cmnf
    wceq
    #
    @40
    cmnf
    wceq
    @49
    @32
    @57
    @59
    wi
    wph
    @32
    @4
    @18
    xblss2.5
    ad2antrr
    @32
    @57
    @59
    cS
    xaddmnf1
    ex
    syl
    @49
    @40
    @58
    cmnf
    @49
    @39
    cmnf
    cS
    cxad
    @49
    @39
    cpnf
    cxne
    #
    cmnf
    @49
    @18
    @39
    @60
    wceq
    @6
    @18
    simpr
    #
    cR
    cpnf
    xnegeq
    syl
    xnegpnf
    syl6eq
    #
    oveq2d
    eqeq1d
    sylibrd
    necon1d
    mpd
    #
    @62
    oveq12d
    pnfaddmnf
    syl6eq
    breqtrd
    @6
    @50
    @51
    wb
    @18
    @6
    @50
    @50
    @55
    wa
    #
    @20
    cc0
    wceq
    #
    @51
    @6
    @55
    @50
    @56
    biantrud
    @6
    @43
    @53
    @65
    @64
    wb
    @29
    0xr
    @20
    cc0
    xrletri3
    sylancl
    @6
    @12
    @13
    @23
    @65
    @51
    wb
    @24
    @35
    @25
    cP
    cQ
    cD
    cX
    xmeteq0
    syl3anc
    3bitr2d
    adantr
    mpbid
    oveq1d
    @49
    cR
    cpnf
    cS
    @61
    @63
    eqtr4d
    3brtr3d
    @6
    @14
    cR
    cmnf
    wne
    #
    wa
    @17
    @18
    wo
    @6
    @14
    @66
    @30
    @6
    @14
    cc0
    cR
    cle
    wbr
    #
    @66
    @30
    @6
    cc0
    cR
    clt
    wbr
    #
    @67
    @6
    cc0
    @10
    cR
    @54
    @36
    @30
    @6
    @12
    @13
    @7
    cc0
    @10
    cle
    wbr
    @24
    @35
    @16
    cP
    @3
    cD
    cX
    xmetge0
    syl3anc
    @38
    xrlelttrd
    @6
    @53
    @14
    @68
    @67
    wi
    0xr
    @30
    cc0
    cR
    xrltle
    sylancr
    mpd
    cR
    ge0nemnf
    syl2anc
    jca
    cR
    xrnemnf
    sylib
    mpjaodan
    @6
    @12
    @23
    @32
    @5
    @7
    @9
    wa
    wb
    @24
    @25
    @46
    @3
    cD
    cQ
    cS
    cX
    elbl
    syl3anc
    mpbir2and
    ex
    ssrdv
end
