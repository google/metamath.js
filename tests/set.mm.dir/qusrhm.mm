include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cmulr.mm"
include "cfv.mm"
include "cur.mm"
include "eqid.mm"
include "simpl.mm"
include "qusring.mm"
include "cqg.mm"
include "co.mm"
include "cec.mm"
include "csubg.mm"
include "wer.mm"
include "clidl.mm"
include "coppr.mm"
include "2idlval.mm"
include "elin2.mm"
include "simplbi.mm"
include "lidlsubg.mm"
include "sylan2.mm"
include "eqger.mm"
include "syl.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "divsfval.mm"
include "wceq.mm"
include "qus1.mm"
include "simprd.mm"
include "eqtrd.mm"
include "cv.mm"
include "cqus.mm"
include "2idlcpbl.mm"
include "ringcl.mm"
include "3expb.mm"
include "adantlr.mm"
include "caovclg.mm"
include "qusmulval.mm"
include "adantr.mm"
include "oveq12d.mm"
include "3eqtr4rd.mm"
include "cnsg.mm"
include "cghm.mm"
include "cabl.mm"
include "ringabl.mm"
include "ablnsg.mm"
include "eleqtrrd.mm"
include "qusghm.mm"
include "isrhm2d.mm"

theorem qusrhm
  let vx: setvar x
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cI: class I
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let c.1: class .1.
  assume qusring.u: |- U = ( R /s ( R ~QG S ) )
  assume qusring.i: |- I = ( 2Ideal ` R )
  assume qusrhm.x: |- X = ( Base ` R )
  assume qusrhm.f: |- F = ( x e. X |-> [ x ] ( R ~QG S ) )

  disjoint I x
  disjoint R x
  disjoint S x
  disjoint U x
  disjoint X x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint I a
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint I b
  disjoint c d
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint I c
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint I d
  disjoint x y
  disjoint x z
  disjoint I y
  disjoint I z
  disjoint .1. c
  disjoint .1. d
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R d
  disjoint R y
  disjoint R z
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S y
  disjoint S z
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U d
  disjoint U y
  disjoint U z
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X y
  disjoint X z
  assert |- ( ( R e. Ring /\ S e. I ) -> F e. ( R RingHom U ) )

  proof
    cR
    crg
    wcel
    #
    cS
    cI
    wcel
    #
    wa
    #
    vy
    vz
    cX
    cR
    cU
    cR
    cmulr
    cfv
    #
    cU
    cmulr
    cfv
    #
    cR
    cur
    cfv
    #
    cF
    cU
    cur
    cfv
    #
    qusrhm.x
    @5
    eqid
    #
    @6
    eqid
    @3
    eqid
    #
    @4
    eqid
    #
    @0
    @1
    simpl
    #
    cR
    cS
    cU
    cI
    qusring.u
    qusring.i
    qusring
    @2
    @5
    cF
    cfv
    @5
    cR
    cS
    cqg
    co
    #
    cec
    #
    @6
    @2
    vx
    @5
    @11
    cF
    cX
    @2
    cS
    cR
    csubg
    cfv
    #
    wcel
    #
    cX
    @11
    wer
    #
    @1
    @0
    cS
    cR
    clidl
    cfv
    #
    wcel
    #
    @14
    @1
    @17
    cS
    cR
    coppr
    cfv
    #
    clidl
    cfv
    #
    wcel
    cS
    @16
    @19
    cI
    cR
    cI
    @16
    @19
    @18
    @16
    eqid
    #
    @18
    eqid
    @19
    eqid
    qusring.i
    2idlval
    elin2
    simplbi
    cR
    @16
    cS
    @20
    lidlsubg
    sylan2
    #
    @11
    cR
    cX
    cS
    qusrhm.x
    @11
    eqid
    #
    eqger
    syl
    #
    cX
    cvv
    wcel
    #
    @2
    cX
    cR
    cbs
    cfv
    #
    cvv
    qusrhm.x
    cR
    cbs
    fvex
    eqeltri
    #
    a1i
    qusrhm.f
    divsfval
    @2
    cU
    crg
    wcel
    @12
    @6
    wceq
    cR
    cS
    cU
    @5
    cI
    qusring.u
    qusring.i
    @7
    qus1
    simprd
    eqtrd
    @2
    vy
    cv
    #
    cX
    wcel
    #
    vz
    cv
    #
    cX
    wcel
    #
    wa
    #
    wa
    #
    @27
    @11
    cec
    #
    @29
    @11
    cec
    #
    @4
    co
    #
    @27
    @29
    @3
    co
    #
    @11
    cec
    #
    @27
    cF
    cfv
    #
    @29
    cF
    cfv
    #
    @4
    co
    @36
    cF
    cfv
    @2
    @28
    @30
    @35
    @37
    wceq
    @2
    @11
    cR
    @4
    @3
    cU
    cX
    @27
    @29
    crg
    vd
    vc
    va
    vb
    cU
    cR
    @11
    cqus
    co
    wceq
    @2
    qusring.u
    a1i
    cX
    @25
    wceq
    @2
    qusrhm.x
    a1i
    @23
    @10
    va
    cv
    vb
    cv
    vc
    cv
    #
    vd
    cv
    #
    cR
    cS
    @3
    @11
    cI
    cX
    qusrhm.x
    @22
    qusring.i
    @8
    2idlcpbl
    @2
    vy
    vz
    @40
    @41
    cX
    cX
    cX
    @3
    @0
    @31
    @36
    cX
    wcel
    #
    @1
    @0
    @28
    @30
    @42
    cX
    cR
    @3
    @27
    @29
    qusrhm.x
    @8
    ringcl
    3expb
    adantlr
    caovclg
    @8
    @9
    qusmulval
    3expb
    @32
    @38
    @33
    @39
    @34
    @4
    @32
    vx
    @27
    @11
    cF
    cX
    @2
    @15
    @31
    @23
    adantr
    #
    @24
    @32
    @26
    a1i
    #
    qusrhm.f
    divsfval
    @32
    vx
    @29
    @11
    cF
    cX
    @43
    @44
    qusrhm.f
    divsfval
    oveq12d
    @32
    vx
    @36
    @11
    cF
    cX
    @43
    @44
    qusrhm.f
    divsfval
    3eqtr4rd
    @2
    cS
    cR
    cnsg
    cfv
    #
    wcel
    cF
    cR
    cU
    cghm
    co
    wcel
    @2
    cS
    @13
    @45
    @21
    @2
    cR
    cabl
    wcel
    #
    @45
    @13
    wceq
    @0
    @46
    @1
    cR
    ringabl
    adantr
    cR
    ablnsg
    syl
    eleqtrrd
    vx
    cF
    cR
    cU
    cX
    cS
    qusrhm.x
    qusring.u
    qusrhm.f
    qusghm
    syl
    isrhm2d
end
