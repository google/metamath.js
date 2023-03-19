include "csca.mm"
include "cfv.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cprds.mm"
include "cmulr.mm"
include "cv.mm"
include "cmpt2.mm"
include "eqid.mm"
include "cxp.mm"
include "crn.mm"
include "cvv.mm"
include "wf1o.mm"
include "wfo.mm"
include "xpsff1o2.mm"
include "f1ocnv.mm"
include "mp1i.mm"
include "f1ofo.mm"
include "syl.mm"
include "f1ocpbl.mm"
include "xpsval.mm"
include "xpslem.mm"
include "ovexd.mm"
include "imasmulval.mm"
include "c2o.mm"
include "wfn.mm"
include "cbs.mm"
include "wcel.mm"
include "w3a.mm"
include "con0.mm"
include "fvexd.mm"
include "2on.mm"
include "a1i.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "prdsmulrval.mm"
include "xpsaddlem.mm"

theorem xpsmul
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vs: setvar s
  let vy: setvar y
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  let vd: setvar d
  let cG: class G
  let cF: class F
  let cU: class U
  let va: setvar a
  let vb: setvar b
  assume xpsval.t: |- T = ( R Xs. S )
  assume xpsval.x: |- X = ( Base ` R )
  assume xpsval.y: |- Y = ( Base ` S )
  assume xpsval.1: |- ( ph -> R e. V )
  assume xpsval.2: |- ( ph -> S e. W )
  assume xpsadd.3: |- ( ph -> A e. X )
  assume xpsadd.4: |- ( ph -> B e. Y )
  assume xpsadd.5: |- ( ph -> C e. X )
  assume xpsadd.6: |- ( ph -> D e. Y )
  assume xpsadd.7: |- ( ph -> ( A .x. C ) e. X )
  assume xpsadd.8: |- ( ph -> ( B .X. D ) e. Y )
  assume xpsmul.m: |- .x. = ( .r ` R )
  assume xpsmul.n: |- .X. = ( .r ` S )
  assume xpsmul.p: |- .xb = ( .r ` T )


  assert |- ( ph -> ( <. A , B >. .xb <. C , D >. ) = <. ( A .x. C ) , ( B .X. D ) >. )

  proof
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    cR
    cS
    c.xb
    cT
    c.x
    c.xp
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
    vk
    cmulr
    vx
    vy
    cX
    cY
    vx
    cv
    csn
    vy
    cv
    csn
    ccda
    co
    ccnv
    cmpt2
    #
    cV
    cW
    cX
    cY
    xpsval.t
    xpsval.x
    xpsval.y
    xpsval.1
    xpsval.2
    xpsadd.3
    xpsadd.4
    xpsadd.5
    xpsadd.6
    xpsadd.7
    xpsadd.8
    xpsmul.m
    xpsmul.n
    xpsmul.p
    @3
    eqid
    #
    @2
    eqid
    #
    wph
    cX
    cY
    cxp
    #
    @2
    c.xb
    @2
    cmulr
    cfv
    #
    cT
    @3
    ccnv
    #
    @3
    crn
    #
    cA
    csn
    cB
    csn
    ccda
    co
    ccnv
    #
    cC
    csn
    cD
    csn
    ccda
    co
    ccnv
    #
    cvv
    vd
    vc
    va
    vb
    wph
    @9
    @6
    @8
    wf1o
    #
    @9
    @6
    @8
    wfo
    @6
    @9
    @3
    wf1o
    @12
    wph
    vx
    vy
    cX
    cY
    @3
    @4
    xpsff1o2
    @6
    @9
    @3
    f1ocnv
    mp1i
    #
    @9
    @6
    @8
    f1ofo
    syl
    wph
    va
    cv
    vb
    cv
    vc
    cv
    vd
    cv
    @7
    @8
    @9
    @6
    @13
    f1ocpbl
    wph
    vx
    vy
    cR
    cS
    cT
    @2
    @3
    @0
    cV
    cW
    cX
    cY
    xpsval.t
    xpsval.x
    xpsval.y
    xpsval.1
    xpsval.2
    @4
    @0
    eqid
    #
    @5
    xpsval
    wph
    vx
    vy
    cR
    cS
    cT
    @2
    @3
    @0
    cV
    cW
    cX
    cY
    xpsval.t
    xpsval.x
    xpsval.y
    xpsval.1
    xpsval.2
    @4
    @14
    @5
    xpslem
    wph
    @0
    @1
    cprds
    ovexd
    @7
    eqid
    #
    xpsmul.p
    imasmulval
    @1
    c2o
    wfn
    #
    @10
    @2
    cbs
    cfv
    #
    wcel
    #
    @11
    @17
    wcel
    #
    w3a
    #
    vk
    @17
    @1
    @0
    @7
    @10
    @11
    c2o
    cvv
    con0
    @2
    @5
    @17
    eqid
    @20
    cR
    csca
    fvexd
    c2o
    con0
    wcel
    @20
    2on
    a1i
    @16
    @18
    @19
    simp1
    @16
    @18
    @19
    simp2
    @16
    @18
    @19
    simp3
    @15
    prdsmulrval
    xpsaddlem
end
