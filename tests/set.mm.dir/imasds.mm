include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cfv.mm"
include "c1st.mm"
include "wceq.mm"
include "c2nd.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cfz.mm"
include "wral.mm"
include "w3a.mm"
include "cxp.mm"
include "cmap.mm"
include "crab.mm"
include "cxrs.mm"
include "ccom.mm"
include "cgsu.mm"
include "cmpt.mm"
include "crn.mm"
include "ciun.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cmpt2.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "csn.mm"
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
include "ccnv.mm"
include "cds.mm"
include "cvv.mm"
include "c2.mm"
include "cdc.mm"
include "eqid.mm"
include "eqidd.mm"
include "imasval.mm"
include "imasvalstr.mm"
include "dsid.mm"
include "snsstp3.mm"
include "ssun2.mm"
include "sstri.mm"
include "wcel.mm"
include "wfo.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "fornex.mm"
include "sylc.mm"
include "mpt2exga.mm"
include "syl2anc.mm"
include "strfv3.mm"

theorem imasds
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cD: class D
  let cR: class R
  let cU: class U
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cV: class V
  let cZ: class Z
  let vp: setvar p
  let vq: setvar q
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cX: class X
  let cK: class K
  let cS: class S
  let cY: class Y
  assume imasbas.u: |- ( ph -> U = ( F "s R ) )
  assume imasbas.v: |- ( ph -> V = ( Base ` R ) )
  assume imasbas.f: |- ( ph -> F : V -onto-> B )
  assume imasbas.r: |- ( ph -> R e. Z )
  assume imasds.e: |- E = ( dist ` R )
  assume imasds.d: |- D = ( dist ` U )

  disjoint g h
  disjoint g i
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint F g
  disjoint h i
  disjoint h n
  disjoint h x
  disjoint h y
  disjoint F h
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint F i
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint R g
  disjoint R h
  disjoint R i
  disjoint R n
  disjoint R x
  disjoint R y
  disjoint U x
  disjoint B x
  disjoint B y
  disjoint E x
  disjoint E y
  disjoint g ph
  disjoint h ph
  disjoint i ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint V g
  disjoint V h
  disjoint g p
  disjoint g q
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g z
  disjoint h p
  disjoint h q
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h z
  disjoint i p
  disjoint i q
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i z
  disjoint n p
  disjoint n q
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n z
  disjoint p q
  disjoint p u
  disjoint p v
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint F p
  disjoint q u
  disjoint q v
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint F q
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
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint R p
  disjoint R q
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R z
  disjoint p ph
  disjoint ph q
  disjoint ph u
  disjoint ph v
  disjoint ph w
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
  disjoint V p
  disjoint V q
  disjoint V w
  disjoint V z
  disjoint Y h
  disjoint Y n
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> D = ( x e. B , y e. B |-> inf ( U_ n e. NN ran ( g e. { h e. ( ( V X. V ) ^m ( 1 ... n ) ) | ( ( F ` ( 1st ` ( h ` 1 ) ) ) = x /\ ( F ` ( 2nd ` ( h ` n ) ) ) = y /\ A. i e. ( 1 ... ( n - 1 ) ) ( F ` ( 2nd ` ( h ` i ) ) ) = ( F ` ( 1st ` ( h ` ( i + 1 ) ) ) ) ) } |-> ( RR*s gsum ( E o. g ) ) ) , RR* , < ) ) )

  proof
    wph
    cD
    vx
    vy
    cB
    cB
    vn
    cn
    vg
    c1
    vh
    cv
    #
    cfv
    c1st
    cfv
    cF
    cfv
    vx
    cv
    wceq
    vn
    cv
    #
    @0
    cfv
    c2nd
    cfv
    cF
    cfv
    vy
    cv
    wceq
    vi
    cv
    #
    @0
    cfv
    c2nd
    cfv
    cF
    cfv
    @2
    c1
    caddc
    co
    @0
    cfv
    c1st
    cfv
    cF
    cfv
    wceq
    vi
    c1
    @1
    c1
    cmin
    co
    cfz
    co
    wral
    w3a
    vh
    cV
    cV
    cxp
    c1
    @1
    cfz
    co
    cmap
    co
    crab
    cxrs
    cE
    vg
    cv
    ccom
    cgsu
    co
    cmpt
    crn
    ciun
    cxr
    clt
    cinf
    #
    cmpt2
    #
    cnx
    cbs
    cfv
    cB
    cop
    cnx
    cplusg
    cfv
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
    @5
    @6
    cR
    cplusg
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
    cnx
    cmulr
    cfv
    vp
    cV
    vq
    cV
    @8
    @5
    @6
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
    ctp
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
    @7
    csn
    @5
    @6
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
    @8
    @5
    @6
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
    #
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
    #
    cnx
    cds
    cfv
    @4
    cop
    #
    ctp
    #
    cun
    #
    cU
    cds
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
    @4
    @9
    @10
    cR
    @12
    @15
    @11
    @16
    cU
    vg
    vh
    vi
    vn
    cE
    cF
    @13
    @17
    @18
    @20
    @14
    @24
    @23
    @21
    cV
    cZ
    vq
    vp
    imasbas.u
    imasbas.v
    @9
    eqid
    @11
    eqid
    @13
    eqid
    @14
    eqid
    @15
    eqid
    @17
    eqid
    @20
    eqid
    imasds.e
    @23
    eqid
    wph
    @10
    eqidd
    wph
    @12
    eqidd
    wph
    @16
    eqidd
    wph
    @18
    eqidd
    wph
    @21
    eqidd
    wph
    @4
    eqidd
    wph
    @24
    eqidd
    imasbas.f
    imasbas.r
    imasval
    cB
    @4
    @10
    @13
    @16
    @12
    @28
    @18
    @24
    @21
    @28
    eqid
    imasvalstr
    dsid
    @26
    csn
    @27
    @28
    @22
    @25
    @26
    snsstp3
    @27
    @19
    ssun2
    sstri
    wph
    cB
    cvv
    wcel
    #
    @29
    @4
    cvv
    wcel
    wph
    cV
    cvv
    wcel
    cV
    cB
    cF
    wfo
    @29
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
    imasbas.f
    cV
    cB
    cvv
    cF
    fornex
    sylc
    #
    @30
    vx
    vy
    cB
    cB
    @3
    cvv
    cvv
    mpt2exga
    syl2anc
    imasds.d
    strfv3
end
