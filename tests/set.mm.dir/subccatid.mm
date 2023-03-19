include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "w3a.mm"
include "cco.mm"
include "cfv.mm"
include "cvv.mm"
include "cbs.mm"
include "ccat.mm"
include "eqid.mm"
include "csubc.mm"
include "subcrcl.mm"
include "syl.mm"
include "subcss1.mm"
include "rescbas.mm"
include "reschom.mm"
include "rescco.mm"
include "cresc.mm"
include "ovex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "biid.mm"
include "adantr.mm"
include "cxp.mm"
include "wfn.mm"
include "simpr.mm"
include "subcidcl.mm"
include "chom.mm"
include "wss.mm"
include "simpr1l.mm"
include "sseldd.mm"
include "simpr1r.mm"
include "subcss2.mm"
include "simpr31.mm"
include "catlid.mm"
include "simpr2l.mm"
include "simpr32.mm"
include "catrid.mm"
include "subccocl.mm"
include "simpr2r.mm"
include "simpr33.mm"
include "catass.mm"
include "iscatd2.mm"

theorem subccatid
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cS: class S
  let c.1: class .1.
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  assume subccat.1: |- D = ( C |`cat J )
  assume subccat.j: |- ( ph -> J e. ( Subcat ` C ) )
  assume subccatid.1: |- ( ph -> J Fn ( S X. S ) )
  assume subccatid.2: |- .1. = ( Id ` C )

  disjoint C x
  disjoint D x
  disjoint ph x
  disjoint .1. x
  disjoint J x
  disjoint S x
  disjoint f g
  disjoint f h
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint C f
  disjoint g h
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint C g
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint C h
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint D g
  disjoint D h
  disjoint D y
  disjoint D z
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint X x
  disjoint .1. f
  disjoint .1. g
  disjoint .1. h
  disjoint .1. w
  disjoint .1. y
  disjoint .1. z
  disjoint J f
  disjoint J g
  disjoint J h
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint S f
  disjoint S g
  disjoint S h
  disjoint S w
  disjoint S y
  disjoint S z
  assert |- ( ph -> ( D e. Cat /\ ( Id ` D ) = ( x e. S |-> ( .1. ` x ) ) ) )

  proof
    wph
    vw
    cv
    #
    cS
    wcel
    #
    vx
    cv
    #
    cS
    wcel
    #
    wa
    #
    vy
    cv
    #
    cS
    wcel
    #
    vz
    cv
    #
    cS
    wcel
    #
    wa
    #
    vf
    cv
    #
    @0
    @2
    cJ
    co
    #
    wcel
    #
    vg
    cv
    #
    @2
    @5
    cJ
    co
    #
    wcel
    #
    vh
    cv
    #
    @5
    @7
    cJ
    co
    #
    wcel
    #
    w3a
    #
    w3a
    #
    vw
    vx
    vy
    vz
    cS
    cD
    cC
    cco
    cfv
    #
    @2
    c.1
    cfv
    vf
    vg
    vh
    cJ
    cvv
    wph
    cC
    cbs
    cfv
    #
    cC
    cD
    cS
    cJ
    ccat
    subccat.1
    @22
    eqid
    #
    wph
    cJ
    cC
    csubc
    cfv
    wcel
    #
    cC
    ccat
    wcel
    #
    subccat.j
    cC
    cJ
    subcrcl
    syl
    #
    subccatid.1
    wph
    @22
    cC
    cS
    cJ
    subccat.j
    subccatid.1
    @23
    subcss1
    #
    rescbas
    wph
    @22
    cC
    cD
    cS
    cJ
    ccat
    subccat.1
    @23
    @26
    subccatid.1
    @27
    reschom
    wph
    @22
    cC
    cD
    cS
    @21
    cJ
    ccat
    subccat.1
    @23
    @26
    subccatid.1
    @27
    @21
    eqid
    #
    rescco
    cD
    cvv
    wcel
    wph
    cD
    cC
    cJ
    cresc
    co
    cvv
    subccat.1
    cC
    cJ
    cresc
    ovex
    eqeltri
    a1i
    @20
    biid
    wph
    @3
    wa
    cC
    cS
    c.1
    cJ
    @2
    wph
    @24
    @3
    subccat.j
    adantr
    wph
    cJ
    cS
    cS
    cxp
    wfn
    #
    @3
    subccatid.1
    adantr
    wph
    @3
    simpr
    subccatid.2
    subcidcl
    wph
    @20
    wa
    #
    @22
    cC
    @21
    c.1
    @10
    cC
    chom
    cfv
    #
    @0
    @2
    @23
    @31
    eqid
    #
    subccatid.2
    wph
    @25
    @20
    @26
    adantr
    #
    @30
    cS
    @22
    @0
    wph
    cS
    @22
    wss
    @20
    @27
    adantr
    #
    @1
    @3
    @9
    @19
    wph
    simpr1l
    #
    sseldd
    #
    @28
    @30
    cS
    @22
    @2
    @34
    @1
    @3
    @9
    @19
    wph
    simpr1r
    #
    sseldd
    #
    @30
    @11
    @0
    @2
    @31
    co
    @10
    @30
    cC
    cS
    @31
    cJ
    @0
    @2
    wph
    @24
    @20
    subccat.j
    adantr
    #
    wph
    @29
    @20
    subccatid.1
    adantr
    #
    @32
    @35
    @37
    subcss2
    @12
    @15
    @18
    @4
    @9
    wph
    simpr31
    #
    sseldd
    #
    catlid
    @30
    @22
    cC
    @21
    c.1
    @13
    @31
    @2
    @5
    @23
    @32
    subccatid.2
    @33
    @38
    @28
    @30
    cS
    @22
    @5
    @34
    @6
    @8
    @4
    @19
    wph
    simpr2l
    #
    sseldd
    #
    @30
    @14
    @2
    @5
    @31
    co
    @13
    @30
    cC
    cS
    @31
    cJ
    @2
    @5
    @39
    @40
    @32
    @37
    @43
    subcss2
    @12
    @15
    @18
    @4
    @9
    wph
    simpr32
    #
    sseldd
    #
    catrid
    @30
    cC
    cS
    @21
    @10
    @13
    cJ
    @0
    @2
    @5
    @39
    @40
    @35
    @28
    @37
    @43
    @41
    @45
    subccocl
    @30
    @22
    cC
    @21
    @10
    @13
    @31
    @16
    @7
    @0
    @2
    @5
    @23
    @32
    @28
    @33
    @36
    @38
    @44
    @42
    @46
    @30
    cS
    @22
    @7
    @34
    @6
    @8
    @4
    @19
    wph
    simpr2r
    #
    sseldd
    @30
    @17
    @5
    @7
    @31
    co
    @16
    @30
    cC
    cS
    @31
    cJ
    @5
    @7
    @39
    @40
    @32
    @43
    @47
    subcss2
    @12
    @15
    @18
    @4
    @9
    wph
    simpr33
    sseldd
    catass
    iscatd2
end
