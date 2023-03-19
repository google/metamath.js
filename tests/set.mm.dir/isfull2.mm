include "cful.mm"
include "co.mm"
include "wbr.mm"
include "cfunc.mm"
include "cv.mm"
include "crn.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wfo.mm"
include "isfull.mm"
include "wcel.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "funcf2.mm"
include "ffn.mm"
include "df-fo.mm"
include "baib.mm"
include "3syl.mm"
include "ralbidva.mm"
include "pm5.32i.mm"
include "bitr4i.mm"

theorem isfull2
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let wph: wff ph
  let cR: class R
  let cX: class X
  let cY: class Y
  assume isfull.b: |- B = ( Base ` C )
  assume isfull.j: |- J = ( Hom ` D )
  assume isfull.h: |- H = ( Hom ` C )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint H x
  disjoint H y
  disjoint J x
  disjoint J y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint B c
  disjoint d f
  disjoint d g
  disjoint d x
  disjoint d y
  disjoint B d
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint C c
  disjoint C d
  disjoint C f
  disjoint C g
  disjoint D c
  disjoint D d
  disjoint D f
  disjoint D g
  disjoint ph x
  disjoint ph y
  disjoint H f
  disjoint J c
  disjoint J d
  disjoint J f
  disjoint J g
  disjoint R f
  disjoint X f
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y x
  disjoint Y y
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  assert |- ( F ( C Full D ) G <-> ( F ( C Func D ) G /\ A. x e. B A. y e. B ( x G y ) : ( x H y ) -onto-> ( ( F ` x ) J ( F ` y ) ) ) )

  proof
    cF
    cG
    cC
    cD
    cful
    co
    wbr
    cF
    cG
    cC
    cD
    cfunc
    co
    wbr
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    #
    crn
    @1
    cF
    cfv
    @2
    cF
    cfv
    cJ
    co
    #
    wceq
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    wa
    @0
    @1
    @2
    cH
    co
    #
    @4
    @3
    wfo
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    wa
    vx
    vy
    cB
    cC
    cD
    cF
    cG
    cJ
    isfull.b
    isfull.j
    isfull
    @0
    @11
    @7
    @0
    @10
    @6
    vx
    cB
    @0
    @1
    cB
    wcel
    #
    wa
    #
    @9
    @5
    vy
    cB
    @13
    @2
    cB
    wcel
    #
    wa
    #
    @8
    @4
    @3
    wf
    @3
    @8
    wfn
    #
    @9
    @5
    wb
    @15
    cB
    cC
    cD
    cF
    cG
    cH
    cJ
    @1
    @2
    isfull.b
    isfull.h
    isfull.j
    @0
    @12
    @14
    simpll
    @0
    @12
    @14
    simplr
    @13
    @14
    simpr
    funcf2
    @8
    @4
    @3
    ffn
    @9
    @16
    @5
    @8
    @4
    @3
    df-fo
    baib
    3syl
    ralbidva
    ralbidva
    pm5.32i
    bitr4i
end
