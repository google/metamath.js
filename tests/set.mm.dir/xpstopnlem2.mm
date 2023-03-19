include "ctps.mm"
include "wcel.mm"
include "wa.mm"
include "csca.mm"
include "cfv.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cprds.mm"
include "ctopn.mm"
include "cqtop.mm"
include "cpt.mm"
include "ctx.mm"
include "ccom.mm"
include "c2o.mm"
include "cvv.mm"
include "con0.mm"
include "eqid.mm"
include "fvexd.mm"
include "2on.mm"
include "a1i.mm"
include "xpscfn.mm"
include "prdstopn.mm"
include "c0.mm"
include "c1o.mm"
include "wfn.mm"
include "wceq.mm"
include "wf.mm"
include "topnfn.mm"
include "dffn2.mm"
include "sylib.mm"
include "fnfco.mm"
include "sylancr.mm"
include "xpsfeq.mm"
include "syl.mm"
include "cpr.mm"
include "0ex.mm"
include "prid1.mm"
include "df2o3.mm"
include "eleqtrri.mm"
include "fvco2.mm"
include "sylancl.mm"
include "xpsc0.mm"
include "adantr.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "eqtrd.mm"
include "sneqd.mm"
include "1on.mm"
include "elexi.mm"
include "prid2.mm"
include "xpsc1.mm"
include "adantl.mm"
include "oveq12d.mm"
include "cnveqd.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "cxp.mm"
include "crn.mm"
include "simpl.mm"
include "simpr.mm"
include "xpsval.mm"
include "xpslem.mm"
include "wf1o.mm"
include "wfo.mm"
include "xpsff1o2.mm"
include "f1ocnv.mm"
include "mp1i.mm"
include "f1ofo.mm"
include "ovexd.mm"
include "imastopn.mm"
include "chmeo.mm"
include "ctopon.mm"
include "istps.mm"
include "xpstopnlem1.mm"
include "hmeocnv.mm"
include "hmeoqtop.mm"
include "3syl.mm"
include "3eqtr4d.mm"

theorem xpstopnlem2
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cJ: class J
  let cK: class K
  let cO: class O
  let cX: class X
  let cY: class Y
  assume xpstps.t: |- T = ( R Xs. S )
  assume xpstopn.j: |- J = ( TopOpen ` R )
  assume xpstopn.k: |- K = ( TopOpen ` S )
  assume xpstopn.o: |- O = ( TopOpen ` T )
  assume xpstopnlem.x: |- X = ( Base ` R )
  assume xpstopnlem.y: |- Y = ( Base ` S )
  assume xpstopnlem.f: |- F = ( x e. X , y e. Y |-> `' ( { x } +c { y } ) )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ( R e. TopSp /\ S e. TopSp ) -> O = ( J tX K ) )

  proof
    cR
    ctps
    wcel
    #
    cS
    ctps
    wcel
    #
    wa
    #
    cR
    csca
    cfv
    #
    cR
    csn
    cS
    csn
    ccda
    co
    ccnv
    #
    cprds
    co
    #
    ctopn
    cfv
    #
    cF
    ccnv
    #
    cqtop
    co
    cJ
    csn
    #
    cK
    csn
    #
    ccda
    co
    #
    ccnv
    #
    cpt
    cfv
    #
    @7
    cqtop
    co
    #
    cO
    cJ
    cK
    ctx
    co
    #
    @2
    @6
    @12
    @7
    cqtop
    @2
    @6
    ctopn
    @4
    ccom
    #
    cpt
    cfv
    @12
    @2
    @4
    @3
    c2o
    @6
    cvv
    con0
    @5
    @5
    eqid
    #
    @2
    cR
    csca
    fvexd
    c2o
    con0
    wcel
    @2
    2on
    a1i
    cR
    cS
    ctps
    ctps
    xpscfn
    #
    @6
    eqid
    #
    prdstopn
    @2
    @15
    @11
    cpt
    @2
    c0
    @15
    cfv
    #
    csn
    #
    c1o
    @15
    cfv
    #
    csn
    #
    ccda
    co
    #
    ccnv
    #
    @15
    @11
    @2
    @15
    c2o
    wfn
    #
    @24
    @15
    wceq
    @2
    ctopn
    cvv
    wfn
    c2o
    cvv
    @4
    wf
    #
    @25
    topnfn
    @2
    @4
    c2o
    wfn
    #
    @26
    @17
    c2o
    @4
    dffn2
    sylib
    cvv
    c2o
    ctopn
    @4
    fnfco
    sylancr
    @15
    xpsfeq
    syl
    @2
    @23
    @10
    @2
    @20
    @8
    @22
    @9
    ccda
    @2
    @19
    cJ
    @2
    @19
    c0
    @4
    cfv
    #
    ctopn
    cfv
    #
    cJ
    @2
    @27
    c0
    c2o
    wcel
    @19
    @29
    wceq
    @17
    c0
    c0
    c1o
    cpr
    #
    c2o
    c0
    c1o
    0ex
    prid1
    df2o3
    eleqtrri
    c2o
    ctopn
    @4
    c0
    fvco2
    sylancl
    @2
    @29
    cR
    ctopn
    cfv
    cJ
    @2
    @28
    cR
    ctopn
    @0
    @28
    cR
    wceq
    @1
    cR
    cS
    ctps
    xpsc0
    adantr
    fveq2d
    xpstopn.j
    syl6eqr
    eqtrd
    sneqd
    @2
    @21
    cK
    @2
    @21
    c1o
    @4
    cfv
    #
    ctopn
    cfv
    #
    cK
    @2
    @27
    c1o
    c2o
    wcel
    @21
    @32
    wceq
    @17
    c1o
    @30
    c2o
    c0
    c1o
    c1o
    con0
    1on
    elexi
    prid2
    df2o3
    eleqtrri
    c2o
    ctopn
    @4
    c1o
    fvco2
    sylancl
    @2
    @32
    cS
    ctopn
    cfv
    cK
    @2
    @31
    cS
    ctopn
    @1
    @31
    cS
    wceq
    @0
    cR
    cS
    ctps
    xpsc1
    adantl
    fveq2d
    xpstopn.k
    syl6eqr
    eqtrd
    sneqd
    oveq12d
    cnveqd
    eqtr3d
    fveq2d
    eqtrd
    oveq1d
    @2
    cX
    cY
    cxp
    #
    @5
    cT
    @7
    @6
    cO
    cF
    crn
    #
    cvv
    @2
    vx
    vy
    cR
    cS
    cT
    @5
    cF
    @3
    ctps
    ctps
    cX
    cY
    xpstps.t
    xpstopnlem.x
    xpstopnlem.y
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    #
    xpstopnlem.f
    @3
    eqid
    #
    @16
    xpsval
    @2
    vx
    vy
    cR
    cS
    cT
    @5
    cF
    @3
    ctps
    ctps
    cX
    cY
    xpstps.t
    xpstopnlem.x
    xpstopnlem.y
    @35
    @36
    xpstopnlem.f
    @37
    @16
    xpslem
    @2
    @34
    @33
    @7
    wf1o
    #
    @34
    @33
    @7
    wfo
    @33
    @34
    cF
    wf1o
    @38
    @2
    vx
    vy
    cX
    cY
    cF
    xpstopnlem.f
    xpsff1o2
    @33
    @34
    cF
    f1ocnv
    mp1i
    @34
    @33
    @7
    f1ofo
    syl
    @2
    @3
    @4
    cprds
    ovexd
    @18
    xpstopn.o
    imastopn
    @2
    cF
    @14
    @12
    chmeo
    co
    wcel
    @7
    @12
    @14
    chmeo
    co
    wcel
    @14
    @13
    wceq
    @2
    vx
    vy
    cF
    cJ
    cK
    cX
    cY
    xpstopnlem.f
    @2
    @0
    cJ
    cX
    ctopon
    cfv
    wcel
    @35
    cX
    cJ
    cR
    xpstopnlem.x
    xpstopn.j
    istps
    sylib
    @2
    @1
    cK
    cY
    ctopon
    cfv
    wcel
    @36
    cY
    cK
    cS
    xpstopnlem.y
    xpstopn.k
    istps
    sylib
    xpstopnlem1
    cF
    @14
    @12
    hmeocnv
    @7
    @12
    @14
    hmeoqtop
    3syl
    3eqtr4d
end
