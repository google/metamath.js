include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cv.mm"
include "cmin.mm"
include "csqrt.mm"
include "cpnf.mm"
include "cico.mm"
include "cres.mm"
include "cfv.mm"
include "cmpt.mm"
include "cc.mm"
include "ccncf.mm"
include "wceq.mm"
include "resqcl.mm"
include "adantr.mm"
include "wss.mm"
include "renegcl.mm"
include "iccssre.mm"
include "mpancom.mm"
include "sselda.mm"
include "resqcld.mm"
include "adantlr.mm"
include "resubcld.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "wi.mm"
include "cabs.mm"
include "3ad2ant1.mm"
include "3ad2ant3.mm"
include "subge0d.mm"
include "absresq.mm"
include "breq1d.mm"
include "bitr4d.mm"
include "recn.mm"
include "abscld.mm"
include "simp1.mm"
include "absge0d.mm"
include "simp2.mm"
include "le2sqd.mm"
include "simp3.mm"
include "absled.mm"
include "3bitr2d.mm"
include "biimprd.mm"
include "3expa.mm"
include "exp4b.mm"
include "3impd.mm"
include "sylbid.mm"
include "imp.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "fvres.mm"
include "syl.mm"
include "mpteq2dva.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "ccn.mm"
include "ctopon.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "resttopon.mm"
include "sylancr.mm"
include "resmptd.mm"
include "a1i.mm"
include "sqcld.mm"
include "cnmptc.mm"
include "sqcn.mm"
include "ctx.mm"
include "subcn.mm"
include "cnmpt12f.mm"
include "toponunii.mm"
include "cnrest.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "crn.mm"
include "wrex.mm"
include "cab.mm"
include "rnmpt.mm"
include "3adant3.mm"
include "eqeltrd.mm"
include "rexlimdv3a.mm"
include "abssdv.mm"
include "syl5eqss.mm"
include "rge0ssre.mm"
include "sstri.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "ssid.mm"
include "cncfss.mm"
include "mp2an.mm"
include "resqrtcn.mm"
include "sselii.mm"
include "cncfcn.mm"
include "eleqtri.mm"
include "cnmpt11f.mm"
include "sylancl.mm"
include "eleqtrrd.mm"

theorem areacirclem2
  let vt: setvar t
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vv: setvar v
  let cS: class S

  disjoint R t
  disjoint x y
  disjoint t x
  disjoint u x
  disjoint v x
  disjoint R x
  disjoint t y
  disjoint u y
  disjoint v y
  disjoint R y
  disjoint t u
  disjoint t v
  disjoint u v
  disjoint R u
  disjoint R v
  disjoint S t
  disjoint S u
  disjoint S v
  assert |- ( ( R e. RR /\ 0 <_ R ) -> ( t e. ( -u R [,] R ) |-> ( sqrt ` ( ( R ^ 2 ) - ( t ^ 2 ) ) ) ) e. ( ( -u R [,] R ) -cn-> CC ) )

  proof
    cR
    cr
    wcel
    #
    cc0
    cR
    cle
    wbr
    #
    wa
    #
    vt
    cR
    cneg
    #
    cR
    cicc
    co
    #
    cR
    c2
    cexp
    co
    #
    vt
    cv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    csqrt
    cc0
    cpnf
    cico
    co
    #
    cres
    #
    cfv
    #
    cmpt
    #
    vt
    @4
    @8
    csqrt
    cfv
    #
    cmpt
    @4
    cc
    ccncf
    co
    #
    @2
    vt
    @4
    @11
    @13
    @2
    @6
    @4
    wcel
    #
    wa
    #
    @8
    @9
    wcel
    #
    @11
    @13
    wceq
    @16
    @8
    cr
    wcel
    cc0
    @8
    cle
    wbr
    #
    @17
    @16
    @5
    @7
    @2
    @5
    cr
    wcel
    #
    @15
    @0
    @19
    @1
    cR
    resqcl
    #
    adantr
    adantr
    @0
    @15
    @7
    cr
    wcel
    #
    @1
    @0
    @15
    wa
    @6
    @0
    @4
    cr
    @6
    @3
    cr
    wcel
    #
    @0
    @4
    cr
    wss
    cR
    renegcl
    #
    @3
    cR
    iccssre
    mpancom
    #
    sselda
    resqcld
    adantlr
    resubcld
    @2
    @15
    @18
    @2
    @15
    @6
    cr
    wcel
    #
    @3
    @6
    cle
    wbr
    #
    @6
    cR
    cle
    wbr
    #
    w3a
    #
    @18
    @0
    @15
    @28
    wb
    #
    @1
    @22
    @0
    @29
    @23
    @3
    cR
    @6
    elicc2
    mpancom
    adantr
    @2
    @25
    @26
    @27
    @18
    @2
    @25
    @26
    @27
    @18
    @0
    @1
    @25
    @26
    @27
    wa
    #
    @18
    wi
    @0
    @1
    @25
    w3a
    #
    @18
    @30
    @31
    @18
    @6
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    @5
    cle
    wbr
    #
    @32
    cR
    cle
    wbr
    @30
    @31
    @18
    @7
    @5
    cle
    wbr
    @34
    @31
    @5
    @7
    @0
    @1
    @19
    @25
    @20
    3ad2ant1
    @25
    @0
    @21
    @1
    @6
    resqcl
    3ad2ant3
    subge0d
    @31
    @33
    @7
    @5
    cle
    @25
    @0
    @33
    @7
    wceq
    @1
    @6
    absresq
    3ad2ant3
    breq1d
    bitr4d
    @31
    @32
    cR
    @25
    @0
    @32
    cr
    wcel
    @1
    @25
    @6
    @6
    recn
    #
    abscld
    3ad2ant3
    @0
    @1
    @25
    simp1
    #
    @25
    @0
    cc0
    @32
    cle
    wbr
    @1
    @25
    @6
    @35
    absge0d
    3ad2ant3
    @0
    @1
    @25
    simp2
    le2sqd
    @31
    @6
    cR
    @0
    @1
    @25
    simp3
    @36
    absled
    3bitr2d
    biimprd
    3expa
    exp4b
    3impd
    sylbid
    imp
    @8
    elrege0
    sylanbrc
    #
    @8
    @9
    csqrt
    fvres
    syl
    mpteq2dva
    @2
    @12
    ccnfld
    ctopn
    cfv
    #
    @4
    crest
    co
    #
    @38
    cc
    crest
    co
    #
    ccn
    co
    #
    @14
    @2
    vt
    @8
    @10
    @39
    @38
    @9
    crest
    co
    #
    @40
    @4
    @0
    @39
    @4
    ctopon
    cfv
    wcel
    #
    @1
    @0
    @38
    cc
    ctopon
    cfv
    wcel
    #
    @4
    cc
    wss
    #
    @43
    @38
    @38
    eqid
    #
    cnfldtopon
    #
    @0
    @4
    cr
    cc
    @24
    ax-resscn
    syl6ss
    #
    @4
    @38
    cc
    resttopon
    sylancr
    adantr
    @2
    vt
    @4
    @8
    cmpt
    #
    @39
    @38
    ccn
    co
    #
    wcel
    #
    @49
    @39
    @42
    ccn
    co
    wcel
    #
    @0
    @51
    @1
    @0
    vt
    cc
    @8
    cmpt
    #
    @4
    cres
    #
    @49
    @50
    @0
    vt
    cc
    @4
    @8
    @48
    resmptd
    @0
    @53
    @38
    @38
    ccn
    co
    #
    wcel
    @45
    @54
    @50
    wcel
    @0
    vt
    @5
    @7
    cmin
    @38
    @38
    @38
    @38
    cc
    @44
    @0
    @47
    a1i
    #
    @0
    vt
    @5
    @38
    @38
    cc
    cc
    @56
    @56
    @0
    cR
    cR
    recn
    sqcld
    cnmptc
    vt
    cc
    @7
    cmpt
    @55
    wcel
    @0
    vt
    @38
    @46
    sqcn
    a1i
    cmin
    @38
    @38
    ctx
    co
    @38
    ccn
    co
    wcel
    @0
    @38
    @46
    subcn
    a1i
    cnmpt12f
    @48
    @4
    @53
    @38
    @38
    cc
    cc
    @38
    @47
    toponunii
    cnrest
    syl2anc
    eqeltrrd
    adantr
    @2
    @44
    @49
    crn
    #
    @9
    wss
    @9
    cc
    wss
    #
    @51
    @52
    wb
    @44
    @2
    @47
    a1i
    @2
    @57
    vu
    cv
    #
    @8
    wceq
    #
    vt
    @4
    wrex
    #
    vu
    cab
    @9
    vt
    vu
    @4
    @8
    @49
    @49
    eqid
    rnmpt
    @2
    @61
    vu
    @9
    @2
    @60
    @59
    @9
    wcel
    vt
    @4
    @2
    @15
    @60
    w3a
    @59
    @8
    @9
    @2
    @15
    @60
    simp3
    @2
    @15
    @17
    @60
    @37
    3adant3
    eqeltrd
    rexlimdv3a
    abssdv
    syl5eqss
    @58
    @2
    @9
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    #
    a1i
    @9
    @49
    @39
    @38
    cc
    cnrest2
    syl3anc
    mpbid
    @10
    @42
    @40
    ccn
    co
    #
    wcel
    @2
    @10
    @9
    cc
    ccncf
    co
    #
    @63
    @9
    cr
    ccncf
    co
    #
    @64
    @10
    cr
    cc
    wss
    cc
    cc
    wss
    #
    @65
    @64
    wss
    ax-resscn
    cc
    ssid
    #
    @9
    cr
    cc
    cncfss
    mp2an
    resqrtcn
    sselii
    @58
    @66
    @64
    @63
    wceq
    @62
    @67
    @9
    cc
    @38
    @42
    @40
    @46
    @42
    eqid
    @40
    eqid
    #
    cncfcn
    mp2an
    eleqtri
    a1i
    cnmpt11f
    @0
    @14
    @41
    wceq
    #
    @1
    @0
    @45
    @66
    @69
    @48
    @67
    @4
    cc
    @38
    @39
    @40
    @46
    @39
    eqid
    @68
    cncfcn
    sylancl
    adantr
    eleqtrrd
    eqeltrrd
end
