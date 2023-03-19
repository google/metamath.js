include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cpsmet.mm"
include "cxr.mm"
include "wb.mm"
include "elblps.mm"
include "syl3anc.mm"
include "simprbda.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cxad.mm"
include "adantr.mm"
include "psmetcl.mm"
include "rexrd.mm"
include "xaddcld.mm"
include "ad2antrr.mm"
include "cle.mm"
include "psmettri2.mm"
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
include "caddc.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "xblpnfps.mm"
include "syl2anc.mm"
include "readdcld.mm"
include "pnfxr.mm"
include "a1i.mm"
include "rexadd.mm"
include "ltpnf.mm"
include "syl.mm"
include "cmnf.mm"
include "wne.mm"
include "cc0.mm"
include "0xr.mm"
include "psmetge0.mm"
include "xrletrd.mm"
include "ge0nemnf.mm"
include "wi.mm"
include "xaddmnf1.mm"
include "ex.mm"
include "xnegeq.mm"
include "xnegpnf.mm"
include "syl6eq.mm"
include "eqeq1d.mm"
include "sylibrd.mm"
include "necon1d.mm"
include "mpd.mm"
include "breqtrrd.mm"
include "wo.mm"
include "xrltle.mm"
include "sylancr.mm"
include "jca.mm"
include "xrnemnf.mm"
include "sylib.mm"
include "mpjaodan.mm"
include "mpbir2and.mm"
include "ssrdv.mm"

theorem xblss2ps
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
  assume xblss2ps.1: |- ( ph -> D e. ( PsMet ` X ) )
  assume xblss2ps.2: |- ( ph -> P e. X )
  assume xblss2ps.3: |- ( ph -> Q e. X )
  assume xblss2ps.4: |- ( ph -> R e. RR* )
  assume xblss2ps.5: |- ( ph -> S e. RR* )
  assume xblss2ps.6: |- ( ph -> ( P D Q ) e. RR )
  assume xblss2ps.7: |- ( ph -> ( P D Q ) <_ ( S +e -e R ) )


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
    cpsmet
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
    xblss2ps.1
    xblss2ps.2
    xblss2ps.4
    @3
    cD
    cP
    cR
    cX
    elblps
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
    xblss2ps.1
    adantr
    #
    wph
    @23
    @4
    xblss2ps.3
    adantr
    #
    @16
    cQ
    @3
    cD
    cX
    psmetcl
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
    xblss2ps.6
    adantr
    #
    rexrd
    #
    wph
    @14
    @4
    xblss2ps.4
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
    xblss2ps.5
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
    xblss2ps.2
    adantr
    #
    @16
    cP
    @3
    cD
    cX
    psmetcl
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
    #
    @24
    @35
    @25
    @16
    cQ
    @3
    cP
    cD
    cX
    psmettri2
    #
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
    @39
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
    @43
    cle
    wbr
    #
    @17
    @6
    @20
    cxr
    wcel
    @42
    cxr
    wcel
    #
    @14
    @20
    @42
    cle
    wbr
    #
    @44
    @29
    @6
    cS
    @41
    wph
    @32
    @4
    xblss2ps.5
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
    @46
    @4
    xblss2ps.7
    adantr
    #
    @20
    @42
    cR
    xleadd1a
    syl31anc
    adantr
    @6
    @32
    @17
    @43
    cS
    wceq
    @47
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
    @8
    cpnf
    cS
    clt
    @50
    @8
    @20
    @10
    caddc
    co
    #
    cpnf
    @6
    @22
    @18
    @26
    adantr
    @50
    @51
    @50
    @20
    @10
    wph
    @27
    @4
    @18
    xblss2ps.6
    ad2antrr
    #
    @50
    wph
    @3
    cP
    cpnf
    @0
    co
    #
    wcel
    #
    @10
    cr
    wcel
    #
    wph
    @4
    @18
    simpll
    @50
    @3
    @1
    @53
    wph
    @4
    @18
    simplr
    @50
    cR
    cpnf
    cP
    @0
    @6
    @18
    simpr
    #
    oveq2d
    eleqtrd
    wph
    @54
    @7
    @55
    wph
    @12
    @13
    @54
    @7
    @55
    wa
    wb
    xblss2ps.1
    xblss2ps.2
    @3
    cD
    cP
    cX
    xblpnfps
    syl2anc
    simplbda
    syl2anc
    #
    readdcld
    #
    rexrd
    cpnf
    cxr
    wcel
    @50
    pnfxr
    a1i
    @50
    @8
    @33
    @51
    cle
    @50
    @12
    @13
    @23
    @7
    @37
    wph
    @12
    @4
    @18
    xblss2ps.1
    ad2antrr
    wph
    @13
    @4
    @18
    xblss2ps.2
    ad2antrr
    wph
    @23
    @4
    @18
    xblss2ps.3
    ad2antrr
    @6
    @7
    @18
    @16
    adantr
    @38
    syl13anc
    @50
    @27
    @55
    @33
    @51
    wceq
    @52
    @57
    @20
    @10
    rexadd
    syl2anc
    breqtrd
    @50
    @51
    cr
    wcel
    @51
    cpnf
    clt
    wbr
    @58
    @51
    ltpnf
    syl
    xrlelttrd
    @50
    @42
    cmnf
    wne
    #
    cS
    cpnf
    wceq
    @6
    @59
    @18
    @6
    @45
    cc0
    @42
    cle
    wbr
    @59
    @48
    @6
    cc0
    @20
    @42
    cc0
    cxr
    wcel
    #
    @6
    0xr
    a1i
    #
    @29
    @48
    @6
    @12
    @13
    @23
    cc0
    @20
    cle
    wbr
    @24
    @35
    @25
    cP
    cQ
    cD
    cX
    psmetge0
    syl3anc
    @49
    xrletrd
    @42
    ge0nemnf
    syl2anc
    adantr
    @50
    cS
    cpnf
    @42
    cmnf
    @50
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
    @42
    cmnf
    wceq
    @50
    @32
    @62
    @64
    wi
    wph
    @32
    @4
    @18
    xblss2ps.5
    ad2antrr
    @32
    @62
    @64
    cS
    xaddmnf1
    ex
    syl
    @50
    @42
    @63
    cmnf
    @50
    @41
    cmnf
    cS
    cxad
    @50
    @41
    cpnf
    cxne
    #
    cmnf
    @50
    @18
    @41
    @65
    wceq
    @56
    cR
    cpnf
    xnegeq
    syl
    xnegpnf
    syl6eq
    oveq2d
    eqeq1d
    sylibrd
    necon1d
    mpd
    breqtrrd
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
    @61
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
    psmetge0
    syl3anc
    @40
    xrlelttrd
    @6
    @60
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
    @47
    @3
    cD
    cQ
    cS
    cX
    elblps
    syl3anc
    mpbir2and
    ex
    ssrdv
end
