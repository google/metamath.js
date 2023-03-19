include "ctx.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "cxp.mm"
include "cv.mm"
include "wss.mm"
include "cioo.mm"
include "crn.mm"
include "cmpt2.mm"
include "wrex.mm"
include "cuni.mm"
include "elunii.mm"
include "ancoms.mm"
include "tpr2uni.mm"
include "syl6eleq.mm"
include "ci.mm"
include "cmul.mm"
include "caddc.mm"
include "eqid.mm"
include "tpr2rico.mm"
include "anass.mm"
include "dya2iocnrect.mm"
include "3expb.mm"
include "anim1i.mm"
include "anasss.mm"
include "sylan2br.mm"
include "r19.41v.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "sstrd.mm"
include "jca.mm"
include "reximi.mm"
include "sylbir.mm"
include "syl.mm"
include "rexlimdvaa.mm"
include "sylc.mm"

theorem dya2iocnei
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cR: class R
  let vn: setvar n
  let cI: class I
  let cJ: class J
  let cX: class X
  let vb: setvar b
  let ve: setvar e
  let vf: setvar f
  let vr: setvar r
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )
  assume dya2ioc.1: |- I = ( x e. ZZ , n e. ZZ |-> ( ( x / ( 2 ^ n ) ) [,) ( ( x + 1 ) / ( 2 ^ n ) ) ) )
  assume dya2ioc.2: |- R = ( u e. ran I , v e. ran I |-> ( u X. v ) )

  disjoint b u
  disjoint b v
  disjoint b x
  disjoint u v
  disjoint u x
  disjoint v x
  disjoint A b
  disjoint I x
  disjoint R b
  disjoint X b
  disjoint X x
  disjoint n x
  disjoint I x
  disjoint u v
  disjoint I u
  disjoint I v
  disjoint u x
  disjoint v x
  disjoint b e
  disjoint b f
  disjoint e f
  disjoint e u
  disjoint e v
  disjoint e x
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint b r
  disjoint e r
  disjoint A e
  disjoint A r
  disjoint J e
  disjoint R e
  disjoint f r
  disjoint R f
  disjoint R r
  disjoint X e
  disjoint X f
  disjoint r x
  disjoint X r
  assert |- ( ( A e. ( J tX J ) /\ X e. A ) -> E. b e. ran R ( X e. b /\ b C_ A ) )

  proof
    cA
    cJ
    cJ
    ctx
    co
    #
    wcel
    #
    cX
    cA
    wcel
    #
    wa
    #
    cX
    cr
    cr
    cxp
    #
    wcel
    #
    cX
    vr
    cv
    #
    wcel
    #
    @6
    cA
    wss
    #
    wa
    #
    vr
    ve
    vf
    cioo
    crn
    #
    @10
    ve
    cv
    vf
    cv
    cxp
    cmpt2
    crn
    #
    wrex
    cX
    vb
    cv
    #
    wcel
    #
    @12
    cA
    wss
    #
    wa
    #
    vb
    cR
    crn
    #
    wrex
    #
    @3
    cX
    @0
    cuni
    #
    @4
    @2
    @1
    cX
    @18
    wcel
    cX
    cA
    @0
    elunii
    ancoms
    cJ
    sxbrsiga.0
    tpr2uni
    syl6eleq
    ve
    vf
    vv
    vu
    cA
    @11
    vu
    vv
    cr
    cr
    vu
    cv
    ci
    vv
    cv
    cmul
    co
    caddc
    co
    cmpt2
    #
    cJ
    cX
    vr
    sxbrsiga.0
    @19
    eqid
    @11
    eqid
    #
    tpr2rico
    @5
    @9
    @17
    vr
    @11
    @5
    @6
    @11
    wcel
    #
    @9
    wa
    #
    wa
    @13
    @12
    @6
    wss
    #
    wa
    #
    vb
    @16
    wrex
    #
    @8
    wa
    #
    @17
    @22
    @5
    @21
    @7
    wa
    #
    @8
    wa
    @26
    @21
    @7
    @8
    anass
    @5
    @27
    @8
    @26
    @5
    @27
    wa
    @25
    @8
    @5
    @21
    @7
    @25
    vx
    vv
    vu
    @6
    @11
    cR
    ve
    vf
    vn
    cI
    cJ
    cX
    vb
    sxbrsiga.0
    dya2ioc.1
    dya2ioc.2
    @20
    dya2iocnrect
    3expb
    anim1i
    anasss
    sylan2br
    @26
    @24
    @8
    wa
    #
    vb
    @16
    wrex
    @17
    @24
    @8
    vb
    @16
    r19.41v
    @28
    @15
    vb
    @16
    @28
    @13
    @14
    @13
    @23
    @8
    simpll
    @28
    @12
    @6
    cA
    @13
    @23
    @8
    simplr
    @24
    @8
    simpr
    sstrd
    jca
    reximi
    sylbir
    syl
    rexlimdvaa
    sylc
end
