include "cdm.mm"
include "wfn.mm"
include "crn.mm"
include "cxp.mm"
include "cpw.mm"
include "wss.mm"
include "wf.mm"
include "wfun.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wwe.mm"
include "cin.mm"
include "co.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wsbc.mm"
include "wral.mm"
include "relopabi.mm"
include "a1i.mm"
include "simprr.mm"
include "fpwwe2lem2.mm"
include "simprbda.mm"
include "simprd.mm"
include "adantrl.mm"
include "adantr.mm"
include "df-ss.mm"
include "sylib.mm"
include "eqtrd.mm"
include "adantrr.mm"
include "eqtr2d.mm"
include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "adantlr.mm"
include "simprl.mm"
include "fpwwe2lem10.mm"
include "mpjaodan.mm"
include "ex.mm"
include "alrimiv.mm"
include "alrimivv.mm"
include "dffun2.mm"
include "sylanbrc.mm"
include "funfn.mm"
include "wex.mm"
include "vex.mm"
include "elrn.mm"
include "cuni.mm"
include "releldmi.mm"
include "adantl.mm"
include "elssuni.mm"
include "syl.mm"
include "syl6sseqr.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "sstrd.mm"
include "selpw.mm"
include "syl6ibr.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "df-f.mm"

theorem fpwwe2lem11
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let cF: class F
  let cW: class W
  let cX: class X
  let vr: setvar r
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let vn: setvar n
  let cM: class M
  let cN: class N
  let cR: class R
  let cY: class Y
  let cS: class S
  assume fpwwe2.1: |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\ ( r We x /\ A. y e. x [. ( `' r " { y } ) / u ]. ( u F ( r i^i ( u X. u ) ) ) = y ) ) }
  assume fpwwe2.2: |- ( ph -> A e. _V )
  assume fpwwe2.3: |- ( ( ph /\ ( x C_ A /\ r C_ ( x X. x ) /\ r We x ) ) -> ( x F r ) e. A )
  assume fpwwe2.4: |- X = U. dom W

  disjoint u y
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint F r
  disjoint u x
  disjoint F u
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint X r
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint ph r
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint A r
  disjoint A x
  disjoint W r
  disjoint W u
  disjoint W x
  disjoint W y
  disjoint B u
  disjoint B y
  disjoint a b
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint F b
  disjoint r s
  disjoint r t
  disjoint r v
  disjoint r w
  disjoint r z
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint F t
  disjoint u v
  disjoint u w
  disjoint u z
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
  disjoint a n
  disjoint X a
  disjoint b n
  disjoint X b
  disjoint n r
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint X n
  disjoint X s
  disjoint X t
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint M r
  disjoint M u
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint N r
  disjoint N u
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint a ph
  disjoint b ph
  disjoint n ph
  disjoint ph s
  disjoint ph t
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint A a
  disjoint A s
  disjoint A t
  disjoint A w
  disjoint A z
  disjoint R r
  disjoint R u
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint Y r
  disjoint Y u
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint S r
  disjoint S u
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint W a
  disjoint W b
  disjoint W n
  disjoint W s
  disjoint W t
  disjoint W v
  disjoint W w
  disjoint W z
  assert |- ( ph -> W : dom W --> ~P ( X X. X ) )

  proof
    wph
    cW
    cW
    cdm
    #
    wfn
    #
    cW
    crn
    #
    cX
    cX
    cxp
    #
    cpw
    #
    wss
    @0
    @4
    cW
    wf
    wph
    cW
    wfun
    #
    @1
    wph
    cW
    wrel
    #
    vw
    cv
    #
    vs
    cv
    #
    cW
    wbr
    #
    @7
    vt
    cv
    #
    cW
    wbr
    #
    wa
    #
    @8
    @10
    wceq
    #
    wi
    #
    vt
    wal
    #
    vs
    wal
    vw
    wal
    @5
    @6
    wph
    vx
    cv
    #
    cA
    wss
    #
    vr
    cv
    #
    @16
    @16
    cxp
    wss
    #
    wa
    @16
    @18
    wwe
    #
    vu
    cv
    #
    @18
    @21
    @21
    cxp
    #
    cin
    cF
    co
    vy
    cv
    #
    wceq
    vu
    @18
    ccnv
    @23
    csn
    #
    cima
    wsbc
    vy
    @16
    wral
    wa
    wa
    vx
    vr
    cW
    fpwwe2.1
    relopabi
    #
    a1i
    wph
    @15
    vw
    vs
    wph
    @14
    vt
    wph
    @12
    @13
    wph
    @12
    wa
    #
    @7
    @7
    wss
    #
    @8
    @10
    @7
    @7
    cxp
    #
    cin
    #
    wceq
    #
    wa
    #
    @13
    @27
    @10
    @8
    @28
    cin
    #
    wceq
    #
    wa
    #
    @26
    @31
    wa
    #
    @8
    @29
    @10
    @26
    @27
    @30
    simprr
    @35
    @10
    @28
    wss
    #
    @29
    @10
    wceq
    @26
    @36
    @31
    wph
    @11
    @36
    @9
    wph
    @11
    wa
    @7
    cA
    wss
    #
    @36
    wph
    @11
    @37
    @36
    wa
    @7
    @10
    wwe
    @21
    @10
    @22
    cin
    cF
    co
    @23
    wceq
    vu
    @10
    ccnv
    @24
    cima
    wsbc
    vy
    @7
    wral
    wa
    wph
    vx
    vy
    vu
    cA
    @10
    cF
    cW
    @7
    vr
    fpwwe2.1
    fpwwe2.2
    fpwwe2lem2
    simprbda
    simprd
    adantrl
    adantr
    @10
    @28
    df-ss
    sylib
    eqtrd
    @26
    @34
    wa
    #
    @10
    @32
    @8
    @26
    @27
    @33
    simprr
    @38
    @8
    @28
    wss
    #
    @32
    @8
    wceq
    @26
    @39
    @34
    wph
    @9
    @39
    @11
    wph
    @9
    wa
    #
    @37
    @39
    wph
    @9
    @37
    @39
    wa
    @7
    @8
    wwe
    @21
    @8
    @22
    cin
    cF
    co
    @23
    wceq
    vu
    @8
    ccnv
    @24
    cima
    wsbc
    vy
    @7
    wral
    wa
    wph
    vx
    vy
    vu
    cA
    @8
    cF
    cW
    @7
    vr
    fpwwe2.1
    fpwwe2.2
    fpwwe2lem2
    simprbda
    simprd
    #
    adantrr
    adantr
    @8
    @28
    df-ss
    sylib
    eqtr2d
    @26
    vx
    vy
    vu
    cA
    @8
    @10
    cF
    cW
    @7
    @7
    vr
    fpwwe2.1
    wph
    cA
    cvv
    wcel
    @12
    fpwwe2.2
    adantr
    wph
    @17
    @19
    @20
    w3a
    @16
    @18
    cF
    co
    cA
    wcel
    @12
    fpwwe2.3
    adantlr
    wph
    @9
    @11
    simprl
    wph
    @9
    @11
    simprr
    fpwwe2lem10
    mpjaodan
    ex
    alrimiv
    alrimivv
    vw
    vs
    vt
    cW
    dffun2
    sylanbrc
    cW
    funfn
    sylib
    wph
    vs
    @2
    @4
    @8
    @2
    wcel
    @9
    vw
    wex
    wph
    @8
    @4
    wcel
    #
    vw
    @8
    cW
    vs
    vex
    elrn
    wph
    @9
    @42
    vw
    wph
    @9
    @8
    @3
    wss
    #
    @42
    wph
    @9
    @43
    @40
    @8
    @28
    @3
    @41
    @40
    @7
    cX
    wss
    #
    @44
    @28
    @3
    wss
    @40
    @7
    @0
    cuni
    #
    cX
    @40
    @7
    @0
    wcel
    #
    @7
    @45
    wss
    @9
    @46
    wph
    @7
    @8
    cW
    @25
    releldmi
    adantl
    @7
    @0
    elssuni
    syl
    fpwwe2.4
    syl6sseqr
    #
    @47
    @7
    cX
    @7
    cX
    xpss12
    syl2anc
    sstrd
    ex
    vs
    @3
    selpw
    syl6ibr
    exlimdv
    syl5bi
    ssrdv
    @0
    @4
    cW
    df-f
    sylanbrc
end
