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
include "eqidd.mm"
include "imasds.mm"
include "imasval.mm"
include "imasvalstr.mm"
include "plusgid.mm"
include "snsstp2.mm"
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

theorem imasplusg
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
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
  assume imasplusg.p: |- .+ = ( +g ` R )
  assume imasplusg.a: |- .+b = ( +g ` U )

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
  assert |- ( ph -> .+b = U_ p e. V U_ q e. V { <. <. ( F ` p ) , ( F ` q ) >. , ( F ` ( p .+ q ) ) >. } )

  proof
    wph
    c.pb
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
    c.pl
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
    @7
    cop
    #
    cnx
    cmulr
    cfv
    vp
    cV
    vq
    cV
    @3
    @0
    @1
    cR
    cmulr
    cfv
    #
    co
    cF
    cfv
    cop
    csn
    ciun
    ciun
    #
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
    @14
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
    cplusg
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
    @26
    c.pl
    @7
    cR
    @11
    @16
    @10
    @17
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
    @14
    @18
    @19
    @22
    @15
    @25
    @24
    @23
    cV
    cZ
    vq
    vp
    imasbas.u
    imasbas.v
    imasplusg.p
    @10
    eqid
    @14
    eqid
    @15
    eqid
    @16
    eqid
    @18
    eqid
    @22
    eqid
    @29
    eqid
    #
    @24
    eqid
    wph
    @7
    eqidd
    wph
    @11
    eqidd
    wph
    @17
    eqidd
    wph
    @19
    eqidd
    wph
    @23
    eqidd
    wph
    vx
    vy
    cB
    @26
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
    @30
    @26
    eqid
    imasds
    wph
    @25
    eqidd
    imasbas.f
    imasbas.r
    imasval
    cB
    @26
    @7
    @14
    @17
    @11
    @28
    @19
    @25
    @23
    @28
    eqid
    imasvalstr
    plusgid
    @9
    csn
    #
    @21
    @28
    @31
    @13
    @21
    @8
    @9
    @12
    snsstp2
    @13
    @20
    ssun1
    sstri
    @21
    @27
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
    @33
    vp
    cV
    wph
    @32
    @5
    cvv
    wcel
    #
    vq
    cV
    wral
    @33
    @34
    @35
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
    imasplusg.a
    strfv3
end
