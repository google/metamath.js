include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cmap.mm"
include "co.mm"
include "cdif.mm"
include "vex.mm"
include "snex.mm"
include "unex.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "cfv.mm"
include "cres.mm"
include "wf.mm"
include "simpr.mm"
include "cvv.mm"
include "wb.mm"
include "elmapex.mm"
include "adantl.mm"
include "elmapg.mm"
include "syl.mm"
include "mpbid.mm"
include "simpl.mm"
include "ffvelrnd.mm"
include "wss.mm"
include "difss.mm"
include "fssres.mm"
include "sylancl.mm"
include "simpld.mm"
include "simprd.mm"
include "difexg.mm"
include "elmapd.mm"
include "mpbird.mm"
include "wfn.mm"
include "ffn.mm"
include "fnsnsplit.mm"
include "syl2anc.mm"
include "opeq2.mm"
include "sneqd.mm"
include "uneq2d.mm"
include "eqeq2d.mm"
include "uneq1.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "ex.mm"
include "cin.mm"
include "c0.mm"
include "elmapi.mm"
include "ad2antll.mm"
include "wf1o.mm"
include "f1osng.mm"
include "f1of.mm"
include "mpan2.mm"
include "adantr.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "a1i.mm"
include "fun.mm"
include "syl21anc.mm"
include "uncom.mm"
include "snssd.mm"
include "undif.mm"
include "sylib.mm"
include "syl5eq.mm"
include "feq2d.mm"
include "ssid.mm"
include "snssi.mm"
include "ad2antrl.mm"
include "unssd.mm"
include "fssd.mm"
include "ssun1.mm"
include "undif1.mm"
include "unexg.mm"
include "syl5eqelr.mm"
include "ssexg.mm"
include "sylancr.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "impbid.mm"
include "ralxpxfr2d.mm"

theorem ralxpmap
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cJ: class J
  assume ralxpmap.j: |- ( f = ( g u. { <. J , y >. } ) -> ( ph <-> ps ) )

  disjoint g ph
  disjoint ph y
  disjoint g y
  disjoint f ps
  disjoint J f
  disjoint J g
  disjoint J y
  disjoint f g
  disjoint f y
  disjoint S f
  disjoint S g
  disjoint S y
  disjoint T f
  disjoint T g
  disjoint T y
  assert |- ( J e. T -> ( A. f e. ( S ^m T ) ph <-> A. y e. S A. g e. ( S ^m ( T \ { J } ) ) ps ) )

  proof
    cJ
    cT
    wcel
    #
    wph
    wps
    vf
    vy
    vg
    vg
    cv
    #
    cJ
    vy
    cv
    #
    cop
    #
    csn
    #
    cun
    #
    cS
    cT
    cmap
    co
    #
    cS
    cS
    cT
    cJ
    csn
    #
    cdif
    #
    cmap
    co
    #
    @1
    @4
    vg
    vex
    @3
    snex
    unex
    @0
    vf
    cv
    #
    @6
    wcel
    #
    @10
    @5
    wceq
    #
    vg
    @9
    wrex
    vy
    cS
    wrex
    #
    @0
    @11
    @13
    @0
    @11
    wa
    #
    cJ
    @10
    cfv
    #
    cS
    wcel
    @10
    @8
    cres
    #
    @9
    wcel
    #
    @10
    @16
    cJ
    @15
    cop
    #
    csn
    #
    cun
    #
    wceq
    #
    @13
    @14
    cT
    cS
    cJ
    @10
    @14
    @11
    cT
    cS
    @10
    wf
    #
    @0
    @11
    simpr
    @14
    cS
    cvv
    wcel
    #
    cT
    cvv
    wcel
    #
    wa
    #
    @11
    @22
    wb
    @11
    @25
    @0
    @10
    cS
    cT
    elmapex
    #
    adantl
    #
    cS
    cT
    @10
    cvv
    cvv
    elmapg
    syl
    mpbid
    #
    @0
    @11
    simpl
    #
    ffvelrnd
    @14
    @17
    @8
    cS
    @16
    wf
    #
    @14
    @22
    @8
    cT
    wss
    @30
    @28
    cT
    @7
    difss
    cT
    cS
    @8
    @10
    fssres
    sylancl
    @14
    cS
    @8
    @16
    cvv
    cvv
    @11
    @23
    @0
    @11
    @23
    @24
    @26
    simpld
    adantl
    @14
    @24
    @8
    cvv
    wcel
    #
    @14
    @23
    @24
    @27
    simprd
    cT
    @7
    cvv
    difexg
    syl
    elmapd
    mpbird
    @14
    @10
    cT
    wfn
    #
    @0
    @21
    @14
    @22
    @32
    @28
    cT
    cS
    @10
    ffn
    syl
    @29
    cT
    @10
    cJ
    fnsnsplit
    syl2anc
    @12
    @21
    @10
    @1
    @19
    cun
    #
    wceq
    vy
    vg
    @15
    @16
    cS
    @9
    @2
    @15
    wceq
    #
    @5
    @33
    @10
    @34
    @4
    @19
    @1
    @34
    @3
    @18
    @2
    @15
    cJ
    opeq2
    sneqd
    uneq2d
    eqeq2d
    @1
    @16
    wceq
    @33
    @20
    @10
    @1
    @16
    @19
    uneq1
    eqeq2d
    rspc2ev
    syl3anc
    ex
    @0
    @12
    @11
    vy
    vg
    cS
    @9
    @0
    @2
    cS
    wcel
    #
    @1
    @9
    wcel
    #
    wa
    #
    wa
    #
    @11
    @12
    @5
    @6
    wcel
    #
    @38
    @39
    cT
    cS
    @5
    wf
    @38
    cT
    cS
    @2
    csn
    #
    cun
    #
    cS
    @5
    @38
    @8
    @7
    cun
    #
    @41
    @5
    wf
    #
    cT
    @41
    @5
    wf
    @38
    @8
    cS
    @1
    wf
    #
    @7
    @40
    @4
    wf
    #
    @8
    @7
    cin
    #
    c0
    wceq
    #
    @43
    @36
    @44
    @0
    @35
    @1
    cS
    @8
    elmapi
    ad2antll
    @0
    @45
    @37
    @0
    @2
    cvv
    wcel
    #
    @45
    vy
    vex
    @0
    @48
    wa
    @7
    @40
    @4
    wf1o
    @45
    cJ
    @2
    cT
    cvv
    f1osng
    @7
    @40
    @4
    f1of
    syl
    mpan2
    adantr
    @47
    @38
    @46
    @7
    @8
    cin
    c0
    @8
    @7
    incom
    @7
    cT
    disjdif
    eqtri
    a1i
    @8
    @7
    cS
    @40
    @1
    @4
    fun
    syl21anc
    @38
    @42
    cT
    @41
    @5
    @38
    @42
    @7
    @8
    cun
    #
    cT
    @8
    @7
    uncom
    @38
    @7
    cT
    wss
    @49
    cT
    wceq
    @38
    cJ
    cT
    @0
    @37
    simpl
    snssd
    @7
    cT
    undif
    sylib
    syl5eq
    feq2d
    mpbid
    @38
    cS
    @40
    cS
    cS
    cS
    wss
    @38
    cS
    ssid
    a1i
    @35
    @40
    cS
    wss
    @0
    @36
    @2
    cS
    snssi
    ad2antrl
    unssd
    fssd
    @38
    cS
    cT
    @5
    cvv
    cvv
    @38
    @23
    @31
    @36
    @23
    @31
    wa
    @0
    @35
    @1
    cS
    @8
    elmapex
    ad2antll
    #
    simpld
    @38
    cT
    cT
    @7
    cun
    #
    wss
    @51
    cvv
    wcel
    @24
    cT
    @7
    ssun1
    @38
    @51
    @42
    cvv
    cT
    @7
    undif1
    @38
    @31
    @7
    cvv
    wcel
    @42
    cvv
    wcel
    @38
    @23
    @31
    @50
    simprd
    cJ
    snex
    @8
    @7
    cvv
    cvv
    unexg
    sylancl
    syl5eqelr
    cT
    @51
    cvv
    ssexg
    sylancr
    elmapd
    mpbird
    @10
    @5
    @6
    eleq1
    syl5ibrcom
    rexlimdvva
    impbid
    @12
    wph
    wps
    wb
    @0
    ralxpmap.j
    adantl
    ralxpxfr2d
end
