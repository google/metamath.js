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
include "imasmulr.mm"
include "imasvsca.mm"
include "eqidd.mm"
include "imasds.mm"
include "imasval.mm"
include "imasvalstr.mm"
include "ipid.mm"
include "snsstp3.mm"
include "ssun2.mm"
include "sstri.mm"
include "ssun1.mm"
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

theorem imasip
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cF: class F
  let c.xi: class .,
  let cI: class I
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
  assume imasip.i: |- ., = ( .i ` R )
  assume imasip.w: |- I = ( .i ` U )

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
  assert |- ( ph -> I = U_ p e. V U_ q e. V { <. <. ( F ` p ) , ( F ` q ) >. , ( p ., q ) >. } )

  proof
    wph
    cI
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
    cop
    @0
    @1
    c.xi
    co
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
    cnx
    cplusg
    cfv
    cU
    cplusg
    cfv
    #
    cop
    cnx
    cmulr
    cfv
    cU
    cmulr
    cfv
    #
    cop
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
    #
    cnx
    cvsca
    cfv
    cU
    cvsca
    cfv
    #
    cop
    #
    cnx
    cip
    cfv
    @5
    cop
    #
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
    cip
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
    @20
    cR
    cplusg
    cfv
    #
    @6
    cR
    @7
    cR
    cvsca
    cfv
    #
    cR
    cmulr
    cfv
    #
    @11
    cU
    vz
    vw
    vv
    vu
    cR
    cds
    cfv
    #
    cF
    @9
    c.xi
    @5
    @16
    @9
    cbs
    cfv
    #
    @19
    @18
    @17
    cV
    cZ
    vq
    vp
    imasbas.u
    imasbas.v
    @23
    eqid
    #
    @25
    eqid
    #
    @9
    eqid
    #
    @27
    eqid
    #
    @24
    eqid
    #
    imasip.i
    @16
    eqid
    @26
    eqid
    #
    @18
    eqid
    wph
    cB
    @23
    @6
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
    @28
    @6
    eqid
    imasplusg
    wph
    cB
    cR
    @7
    @25
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
    @29
    @7
    eqid
    imasmulr
    wph
    vx
    cB
    cR
    @11
    @24
    cU
    cF
    @9
    @27
    cV
    cZ
    vq
    vp
    imasbas.u
    imasbas.v
    imasbas.f
    imasbas.r
    @30
    @31
    @32
    @11
    eqid
    imasvsca
    wph
    @5
    eqidd
    wph
    @17
    eqidd
    wph
    vx
    vy
    cB
    @20
    cR
    cU
    vz
    vw
    vv
    vu
    @26
    cF
    cV
    cZ
    imasbas.u
    imasbas.v
    imasbas.f
    imasbas.r
    @33
    @20
    eqid
    imasds
    wph
    @19
    eqidd
    imasbas.f
    imasbas.r
    imasval
    cB
    @20
    @6
    @9
    @11
    @7
    @22
    @5
    @19
    @17
    @22
    eqid
    imasvalstr
    ipid
    @13
    csn
    #
    @15
    @22
    @34
    @14
    @15
    @10
    @12
    @13
    snsstp3
    @14
    @8
    ssun2
    sstri
    @15
    @21
    ssun1
    sstri
    wph
    cV
    cvv
    wcel
    #
    @4
    cvv
    wcel
    #
    vp
    cV
    wral
    @5
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
    @36
    vp
    cV
    wph
    @35
    @3
    cvv
    wcel
    #
    vq
    cV
    wral
    @36
    @37
    @38
    vq
    cV
    @2
    snex
    rgenw
    vq
    cV
    @3
    cvv
    cvv
    iunexg
    sylancl
    ralrimivw
    vp
    cV
    @4
    cvv
    cvv
    iunexg
    syl2anc
    imasip.w
    strfv3
end
