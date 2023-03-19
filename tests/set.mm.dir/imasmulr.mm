include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "co.mm"
include "csn.mm"
include "ciun.mm"
include "cnx.mm"
include "cbs.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "cmpt2.mm"
include "cip.mm"
include "cun.mm"
include "cts.mm"
include "ctopn.mm"
include "cqtop.mm"
include "cple.mm"
include "ccom.mm"
include "ccnv.mm"
include "cds.mm"
include "cvv.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "eqid.mm"
include "imasplusg.mm"
include "eqidd.mm"
include "imasds.mm"
include "imasval.mm"
include "imasvalstr.mm"
include "mulrid.mm"
include "snsstp3.mm"
include "ssun1.mm"
include "sstri.mm"
include "wcel.mm"
include "wral.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "snex.mm"
include "rgenw.mm"
include "iunexg.mm"
include "sylancl.mm"
include "ralrimivw.mm"
include "syl2anc.mm"
include "strfv3.mm"

theorem imasmulr
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cV: class V
  let cZ: class Z
  let vq: setvar q
  let vp: setvar p
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cE: class E
  let cX: class X
  let cK: class K
  let cS: class S
  let cY: class Y
  assume imasbas.u: |- ( ph -> U = ( F "s R ) )
  assume imasbas.v: |- ( ph -> V = ( Base ` R ) )
  assume imasbas.f: |- ( ph -> F : V -onto-> B )
  assume imasbas.r: |- ( ph -> R e. Z )
  assume imasmulr.p: |- .x. = ( .r ` R )
  assume imasmulr.t: |- .xb = ( .r ` U )

  disjoint p q
  disjoint F p
  disjoint F q
  disjoint R p
  disjoint R q
  disjoint p ph
  disjoint ph q
  disjoint V p
  disjoint V q
  disjoint g h
  disjoint g i
  disjoint g n
  disjoint g p
  disjoint g q
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint h i
  disjoint h n
  disjoint h p
  disjoint h q
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint F h
  disjoint i n
  disjoint i p
  disjoint i q
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint F i
  disjoint n p
  disjoint n q
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint p u
  disjoint p v
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q u
  disjoint q v
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint R g
  disjoint R h
  disjoint R i
  disjoint R n
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint U x
  disjoint B x
  disjoint B y
  disjoint E x
  disjoint E y
  disjoint g ph
  disjoint h ph
  disjoint i ph
  disjoint n ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint X h
  disjoint X n
  disjoint X x
  disjoint X y
  disjoint K p
  disjoint K x
  disjoint S g
  disjoint S x
  disjoint S y
  disjoint V g
  disjoint V h
  disjoint V w
  disjoint V z
  disjoint Y h
  disjoint Y n
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> .xb = U_ p e. V U_ q e. V { <. <. ( F ` p ) , ( F ` q ) >. , ( F ` ( p .x. q ) ) >. } )

  proof
    wph
    c.xb
    vp
    cV
    vq
    cV
    vp
    cv
    #
    cF
    cfv
    vq
    cv
    #
    cF
    cfv
    #
    cop
    #
    @0
    @1
    c.x
    co
    cF
    cfv
    cop
    #
    csn
    #
    ciun
    #
    ciun
    #
    cnx
    cbs
    cfv
    cB
    cop
    #
    cnx
    cplusg
    cfv
    cU
    cplusg
    cfv
    #
    cop
    #
    cnx
    cmulr
    cfv
    @7
    cop
    #
    ctp
    #
    cnx
    csca
    cfv
    cR
    csca
    cfv
    #
    cop
    cnx
    cvsca
    cfv
    vq
    cV
    vp
    vx
    @13
    cbs
    cfv
    #
    @2
    csn
    @0
    @1
    cR
    cvsca
    cfv
    #
    co
    cF
    cfv
    cmpt2
    ciun
    #
    cop
    cnx
    cip
    cfv
    vp
    cV
    vq
    cV
    @3
    @0
    @1
    cR
    cip
    cfv
    #
    co
    cop
    csn
    ciun
    ciun
    #
    cop
    ctp
    #
    cun
    #
    cnx
    cts
    cfv
    cR
    ctopn
    cfv
    #
    cF
    cqtop
    co
    #
    cop
    cnx
    cple
    cfv
    cF
    cR
    cple
    cfv
    #
    ccom
    cF
    ccnv
    ccom
    #
    cop
    cnx
    cds
    cfv
    cU
    cds
    cfv
    #
    cop
    ctp
    #
    cun
    #
    cU
    cmulr
    cvv
    c1
    c1
    c2
    cdc
    cop
    wph
    vx
    vy
    cB
    @25
    cR
    cplusg
    cfv
    #
    @9
    cR
    @7
    @15
    c.x
    @16
    cU
    vg
    vh
    vi
    vn
    cR
    cds
    cfv
    #
    cF
    @13
    @17
    @18
    @21
    @14
    @24
    @23
    @22
    cV
    cZ
    vq
    vp
    imasbas.u
    imasbas.v
    @28
    eqid
    #
    imasmulr.p
    @13
    eqid
    @14
    eqid
    @15
    eqid
    @17
    eqid
    @21
    eqid
    @29
    eqid
    #
    @23
    eqid
    wph
    cB
    @28
    @9
    cR
    cU
    cF
    cV
    cZ
    vq
    vp
    imasbas.u
    imasbas.v
    imasbas.f
    imasbas.r
    @30
    @9
    eqid
    imasplusg
    wph
    @7
    eqidd
    wph
    @16
    eqidd
    wph
    @18
    eqidd
    wph
    @22
    eqidd
    wph
    vx
    vy
    cB
    @25
    cR
    cU
    vg
    vh
    vi
    vn
    @29
    cF
    cV
    cZ
    imasbas.u
    imasbas.v
    imasbas.f
    imasbas.r
    @31
    @25
    eqid
    imasds
    wph
    @24
    eqidd
    imasbas.f
    imasbas.r
    imasval
    cB
    @25
    @9
    @13
    @16
    @7
    @27
    @18
    @24
    @22
    @27
    eqid
    imasvalstr
    mulrid
    @11
    csn
    #
    @20
    @27
    @32
    @12
    @20
    @8
    @10
    @11
    snsstp3
    @12
    @19
    ssun1
    sstri
    @20
    @26
    ssun1
    sstri
    wph
    cV
    cvv
    wcel
    #
    @6
    cvv
    wcel
    #
    vp
    cV
    wral
    @7
    cvv
    wcel
    wph
    cV
    cR
    cbs
    cfv
    cvv
    imasbas.v
    cR
    cbs
    fvex
    syl6eqel
    #
    wph
    @34
    vp
    cV
    wph
    @33
    @5
    cvv
    wcel
    #
    vq
    cV
    wral
    @34
    @35
    @36
    vq
    cV
    @4
    snex
    rgenw
    vq
    cV
    @5
    cvv
    cvv
    iunexg
    sylancl
    ralrimivw
    vp
    cV
    @6
    cvv
    cvv
    iunexg
    syl2anc
    imasmulr.t
    strfv3
end
