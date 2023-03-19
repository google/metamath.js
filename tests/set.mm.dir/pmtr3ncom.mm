include "cv.mm"
include "wne.mm"
include "w3a.mm"
include "wrex.mm"
include "wcel.mm"
include "c3.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "ccom.mm"
include "crn.mm"
include "hashge3el3dif.mm"
include "wi.mm"
include "cpr.mm"
include "wss.mm"
include "c2o.mm"
include "cen.mm"
include "simprl.mm"
include "prssi.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "simplll.mm"
include "simplr.mm"
include "simpr1.mm"
include "pr2nelem.mm"
include "syl3anc.mm"
include "eqid.mm"
include "pmtrrn.mm"
include "adantll.mm"
include "simpr3.mm"
include "df-3an.mm"
include "biimpri.mm"
include "pmtr3ncomlem2.mm"
include "wceq.mm"
include "coeq2.mm"
include "coeq1.mm"
include "neeq12d.mm"
include "rspc2ev.mm"
include "exp31.mm"
include "rexlimdva.mm"
include "rexlimivv.mm"
include "mpcom.mm"

theorem pmtr3ncom
  let cD: class D
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pmtr3ncom.t: |- T = ( pmTrsp ` D )

  disjoint D f
  disjoint D g
  disjoint f g
  disjoint T f
  disjoint T g
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint V x
  disjoint V y
  disjoint V z
  assert |- ( ( D e. V /\ 3 <_ ( # ` D ) ) -> E. f e. ran T E. g e. ran T ( g o. f ) =/= ( f o. g ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    @0
    vz
    cv
    #
    wne
    #
    @1
    @3
    wne
    #
    w3a
    #
    vz
    cD
    wrex
    #
    vy
    cD
    wrex
    vx
    cD
    wrex
    cD
    cV
    wcel
    #
    c3
    cD
    chash
    cfv
    cle
    wbr
    #
    wa
    #
    vg
    cv
    #
    vf
    cv
    #
    ccom
    #
    @12
    @11
    ccom
    #
    wne
    #
    vg
    cT
    crn
    #
    wrex
    vf
    @16
    wrex
    #
    vx
    vy
    vz
    cD
    cV
    hashge3el3dif
    @7
    @10
    @17
    wi
    #
    vx
    vy
    cD
    cD
    @0
    cD
    wcel
    #
    @1
    cD
    wcel
    #
    wa
    #
    @6
    @18
    vz
    cD
    @21
    @3
    cD
    wcel
    #
    wa
    #
    @6
    @10
    @17
    @23
    @6
    wa
    #
    @10
    wa
    #
    @0
    @1
    cpr
    #
    cT
    cfv
    #
    @16
    wcel
    #
    @1
    @3
    cpr
    #
    cT
    cfv
    #
    @16
    wcel
    #
    @30
    @27
    ccom
    #
    @27
    @30
    ccom
    #
    wne
    #
    @17
    @25
    @8
    @26
    cD
    wss
    #
    @26
    c2o
    cen
    wbr
    #
    @28
    @24
    @8
    @9
    simprl
    #
    @23
    @35
    @6
    @10
    @21
    @35
    @22
    @0
    @1
    cD
    prssi
    adantr
    ad2antrr
    @24
    @36
    @10
    @24
    @19
    @20
    @2
    @36
    @19
    @20
    @22
    @6
    simplll
    @23
    @20
    @6
    @19
    @20
    @22
    simplr
    adantr
    #
    @23
    @2
    @4
    @5
    simpr1
    @0
    @1
    cD
    cD
    pr2nelem
    syl3anc
    adantr
    cD
    @26
    @16
    cT
    cV
    pmtr3ncom.t
    @16
    eqid
    #
    pmtrrn
    syl3anc
    @25
    @8
    @29
    cD
    wss
    #
    @29
    c2o
    cen
    wbr
    #
    @31
    @37
    @23
    @40
    @6
    @10
    @20
    @22
    @40
    @19
    @1
    @3
    cD
    prssi
    adantll
    ad2antrr
    @24
    @41
    @10
    @24
    @20
    @22
    @5
    @41
    @38
    @21
    @22
    @6
    simplr
    @23
    @2
    @4
    @5
    simpr3
    @1
    @3
    cD
    cD
    pr2nelem
    syl3anc
    adantr
    cD
    @29
    @16
    cT
    cV
    pmtr3ncom.t
    @39
    pmtrrn
    syl3anc
    @25
    @8
    @19
    @20
    @22
    w3a
    #
    @6
    @34
    @37
    @23
    @42
    @6
    @10
    @42
    @23
    @19
    @20
    @22
    df-3an
    biimpri
    ad2antrr
    @23
    @6
    @10
    simplr
    cD
    cT
    @27
    @30
    cV
    @0
    @1
    @3
    pmtr3ncom.t
    @27
    eqid
    @30
    eqid
    pmtr3ncomlem2
    syl3anc
    @15
    @34
    @11
    @27
    ccom
    #
    @27
    @11
    ccom
    #
    wne
    vf
    vg
    @27
    @30
    @16
    @16
    @12
    @27
    wceq
    @13
    @43
    @14
    @44
    @12
    @27
    @11
    coeq2
    @12
    @27
    @11
    coeq1
    neeq12d
    @11
    @30
    wceq
    @43
    @32
    @44
    @33
    @11
    @30
    @27
    coeq1
    @11
    @30
    @27
    coeq2
    neeq12d
    rspc2ev
    syl3anc
    exp31
    rexlimdva
    rexlimivv
    mpcom
end
