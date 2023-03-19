include "cfth.mm"
include "co.mm"
include "wbr.mm"
include "cfunc.mm"
include "cv.mm"
include "ccnv.mm"
include "wfun.mm"
include "wral.mm"
include "wa.mm"
include "cfv.mm"
include "wf1.mm"
include "isfth.mm"
include "wcel.mm"
include "wf.mm"
include "wb.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "funcf2.mm"
include "df-f1.mm"
include "baib.mm"
include "syl.mm"
include "ralbidva.mm"
include "pm5.32i.mm"
include "bitr4i.mm"

theorem isfth2
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
  let cX: class X
  let cY: class Y
  assume isfth.b: |- B = ( Base ` C )
  assume isfth.h: |- H = ( Hom ` C )
  assume isfth.j: |- J = ( Hom ` D )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint J x
  disjoint J y
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
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( F ( C Faith D ) G <-> ( F ( C Func D ) G /\ A. x e. B A. y e. B ( x G y ) : ( x H y ) -1-1-> ( ( F ` x ) J ( F ` y ) ) ) )

  proof
    cF
    cG
    cC
    cD
    cfth
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
    ccnv
    wfun
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
    @1
    cF
    cfv
    @2
    cF
    cfv
    cJ
    co
    #
    @3
    wf1
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
    isfth.b
    isfth
    @0
    @11
    @6
    @0
    @10
    @5
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
    @4
    vy
    cB
    @13
    @2
    cB
    wcel
    #
    wa
    #
    @7
    @8
    @3
    wf
    #
    @9
    @4
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
    isfth.b
    isfth.h
    isfth.j
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
    @9
    @16
    @4
    @7
    @8
    @3
    df-f1
    baib
    syl
    ralbidva
    ralbidva
    pm5.32i
    bitr4i
end
