include "cga.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "chash.mm"
include "cfv.mm"
include "cqs.mm"
include "cmul.mm"
include "cec.mm"
include "csubg.mm"
include "gastacl.mm"
include "adantr.mm"
include "simpr.mm"
include "lagsubg2.mm"
include "wceq.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "cop.mm"
include "cmpt.mm"
include "crn.mm"
include "wf1o.mm"
include "eqid.mm"
include "orbsta.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "qsex.mm"
include "f1oen.mm"
include "syl.mm"
include "wb.mm"
include "cpw.mm"
include "wss.mm"
include "pwfi.mm"
include "sylib.mm"
include "wer.mm"
include "eqger.mm"
include "qsss.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "ensymd.mm"
include "enfii.mm"
include "hashen.mm"
include "mpbird.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem orbsta2
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let c.po: class .(+)
  let c.sm: class .~
  let vg: setvar g
  let cG: class G
  let cH: class H
  let cO: class O
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume orbsta2.x: |- X = ( Base ` G )
  assume orbsta2.h: |- H = { u e. X | ( u .(+) A ) = A }
  assume orbsta2.r: |- .~ = ( G ~QG H )
  assume orbsta2.o: |- O = { <. x , y >. | ( { x , y } C_ Y /\ E. g e. X ( g .(+) x ) = y ) }

  disjoint g u
  disjoint g x
  disjoint g y
  disjoint .(+) g
  disjoint u x
  disjoint u y
  disjoint .(+) u
  disjoint x y
  disjoint .(+) x
  disjoint .(+) y
  disjoint A g
  disjoint A u
  disjoint A x
  disjoint A y
  disjoint G g
  disjoint G u
  disjoint G x
  disjoint G y
  disjoint Y g
  disjoint Y x
  disjoint Y y
  disjoint .~ g
  disjoint .~ x
  disjoint .~ y
  disjoint H x
  disjoint H y
  disjoint X g
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint g k
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint .(+) k
  disjoint A k
  disjoint G k
  disjoint Y k
  disjoint .~ k
  disjoint O k
  disjoint X k
  assert |- ( ( ( .(+) e. ( G GrpAct Y ) /\ A e. Y ) /\ X e. Fin ) -> ( # ` X ) = ( ( # ` [ A ] O ) x. ( # ` H ) ) )

  proof
    c.po
    cG
    cY
    cga
    co
    wcel
    cA
    cY
    wcel
    wa
    #
    cX
    cfn
    wcel
    #
    wa
    #
    cX
    chash
    cfv
    cX
    c.sm
    cqs
    #
    chash
    cfv
    #
    cH
    chash
    cfv
    #
    cmul
    co
    cA
    cO
    cec
    #
    chash
    cfv
    #
    @5
    cmul
    co
    @2
    c.sm
    cG
    cX
    cH
    orbsta2.x
    orbsta2.r
    @0
    cH
    cG
    csubg
    cfv
    wcel
    #
    @1
    vu
    cA
    c.po
    cG
    cH
    cX
    cY
    orbsta2.x
    orbsta2.h
    gastacl
    adantr
    #
    @0
    @1
    simpr
    #
    lagsubg2
    @2
    @4
    @7
    @5
    cmul
    @2
    @4
    @7
    wceq
    #
    @3
    @6
    cen
    wbr
    #
    @2
    @3
    @6
    vk
    cX
    vk
    cv
    #
    c.sm
    cec
    @13
    cA
    c.po
    co
    cop
    cmpt
    crn
    #
    wf1o
    #
    @12
    @0
    @15
    @1
    vx
    vy
    vu
    cA
    c.po
    c.sm
    vg
    vk
    @14
    cG
    cH
    cO
    cX
    cY
    orbsta2.x
    orbsta2.h
    orbsta2.r
    @14
    eqid
    orbsta2.o
    orbsta
    adantr
    @3
    @6
    @14
    cX
    c.sm
    cX
    cG
    cbs
    cfv
    cvv
    orbsta2.x
    cG
    cbs
    fvex
    eqeltri
    qsex
    f1oen
    syl
    #
    @2
    @3
    cfn
    wcel
    #
    @6
    cfn
    wcel
    #
    @11
    @12
    wb
    @2
    cX
    cpw
    #
    cfn
    wcel
    #
    @3
    @19
    wss
    @17
    @2
    @1
    @20
    @10
    cX
    pwfi
    sylib
    @2
    cX
    c.sm
    @2
    @8
    cX
    c.sm
    wer
    @9
    c.sm
    cG
    cX
    cH
    orbsta2.x
    orbsta2.r
    eqger
    syl
    qsss
    @19
    @3
    ssfi
    syl2anc
    #
    @2
    @17
    @6
    @3
    cen
    wbr
    @18
    @21
    @2
    @3
    @6
    @16
    ensymd
    @6
    @3
    enfii
    syl2anc
    @3
    @6
    hashen
    syl2anc
    mpbird
    oveq1d
    eqtrd
end
