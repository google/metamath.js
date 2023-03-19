include "cv.mm"
include "cfv.mm"
include "csn.mm"
include "co.mm"
include "cmpt2.mm"
include "ciun.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
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
include "fveq2i.mm"
include "eqtri.mm"
include "imasplusg.mm"
include "imasmulr.mm"
include "eqidd.mm"
include "imasds.mm"
include "imasval.mm"
include "imasvalstr.mm"
include "vscaid.mm"
include "snsstp2.mm"
include "ssun2.mm"
include "ssun1.mm"
include "sstri.mm"
include "wcel.mm"
include "wral.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "eqeltri.mm"
include "snex.mm"
include "mpt2ex.mm"
include "rgenw.mm"
include "iunexg.mm"
include "sylancl.mm"
include "strfv3.mm"

theorem imasvsca
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cG: class G
  let cK: class K
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
  let vy: setvar y
  let vz: setvar z
  let cE: class E
  let cX: class X
  let cS: class S
  let cY: class Y
  assume imasbas.u: |- ( ph -> U = ( F "s R ) )
  assume imasbas.v: |- ( ph -> V = ( Base ` R ) )
  assume imasbas.f: |- ( ph -> F : V -onto-> B )
  assume imasbas.r: |- ( ph -> R e. Z )
  assume imassca.g: |- G = ( Scalar ` R )
  assume imasvsca.k: |- K = ( Base ` G )
  assume imasvsca.q: |- .x. = ( .s ` R )
  assume imasvsca.s: |- .xb = ( .s ` U )

  disjoint p q
  disjoint p x
  disjoint F p
  disjoint q x
  disjoint F q
  disjoint F x
  disjoint R p
  disjoint R q
  disjoint R x
  disjoint U x
  disjoint B x
  disjoint p ph
  disjoint ph q
  disjoint ph x
  disjoint K p
  disjoint K x
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
  disjoint p y
  disjoint p z
  disjoint q u
  disjoint q v
  disjoint q w
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
  disjoint R y
  disjoint R z
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
  disjoint ph y
  disjoint ph z
  disjoint X h
  disjoint X n
  disjoint X x
  disjoint X y
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
  assert |- ( ph -> .xb = U_ q e. V ( p e. K , x e. { ( F ` q ) } |-> ( F ` ( p .x. q ) ) ) )

  proof
    wph
    c.xb
    vq
    cV
    vp
    vx
    cK
    vq
    cv
    #
    cF
    cfv
    #
    csn
    #
    vp
    cv
    #
    @0
    c.x
    co
    cF
    cfv
    #
    cmpt2
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
    @6
    cop
    #
    cnx
    cip
    cfv
    vp
    cV
    vq
    cV
    @3
    cF
    cfv
    @1
    cop
    @3
    @0
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
    cvsca
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
    @22
    cR
    cplusg
    cfv
    #
    @7
    cR
    @8
    c.x
    cR
    cmulr
    cfv
    #
    @6
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
    @10
    @13
    @14
    @18
    cK
    @21
    @20
    @19
    cV
    cZ
    vq
    vp
    imasbas.u
    imasbas.v
    @25
    eqid
    #
    @26
    eqid
    #
    @10
    eqid
    cK
    cG
    cbs
    cfv
    #
    @10
    cbs
    cfv
    imasvsca.k
    cG
    @10
    cbs
    imassca.g
    fveq2i
    eqtri
    imasvsca.q
    @13
    eqid
    @18
    eqid
    @27
    eqid
    #
    @20
    eqid
    wph
    cB
    @25
    @7
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
    @7
    eqid
    imasplusg
    wph
    cB
    cR
    @8
    @26
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
    @8
    eqid
    imasmulr
    wph
    @6
    eqidd
    wph
    @14
    eqidd
    wph
    @19
    eqidd
    wph
    vx
    vy
    cB
    @22
    cR
    cU
    vz
    vw
    vv
    vu
    @27
    cF
    cV
    cZ
    imasbas.u
    imasbas.v
    imasbas.f
    imasbas.r
    @31
    @22
    eqid
    imasds
    wph
    @21
    eqidd
    imasbas.f
    imasbas.r
    imasval
    cB
    @22
    @7
    @10
    @6
    @8
    @24
    @14
    @21
    @19
    @24
    eqid
    imasvalstr
    vscaid
    @12
    csn
    @16
    @24
    @11
    @12
    @15
    snsstp2
    @16
    @17
    @24
    @16
    @9
    ssun2
    @17
    @23
    ssun1
    sstri
    sstri
    wph
    cV
    cvv
    wcel
    @5
    cvv
    wcel
    #
    vq
    cV
    wral
    @6
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
    @32
    vq
    cV
    vp
    vx
    cK
    @2
    @4
    cK
    @30
    cvv
    imasvsca.k
    cG
    cbs
    fvex
    eqeltri
    @1
    snex
    mpt2ex
    rgenw
    vq
    cV
    @5
    cvv
    cvv
    iunexg
    sylancl
    imasvsca.s
    strfv3
end
