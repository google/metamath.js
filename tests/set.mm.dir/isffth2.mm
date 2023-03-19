include "cful.mm"
include "co.mm"
include "wbr.mm"
include "cfth.mm"
include "wa.mm"
include "cfunc.mm"
include "cv.mm"
include "cfv.mm"
include "wfo.mm"
include "wral.mm"
include "wf1.mm"
include "cin.mm"
include "wf1o.mm"
include "isfull2.mm"
include "isfth2.mm"
include "anbi12i.mm"
include "brin.mm"
include "df-f1o.mm"
include "ancom.mm"
include "bitri.mm"
include "2ralbii.mm"
include "r19.26-2.mm"
include "anbi2i.mm"
include "anandi.mm"
include "3bitr4i.mm"

theorem isffth2
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
  assert |- ( F ( ( C Full D ) i^i ( C Faith D ) ) G <-> ( F ( C Func D ) G /\ A. x e. B A. y e. B ( x G y ) : ( x H y ) -1-1-onto-> ( ( F ` x ) J ( F ` y ) ) ) )

  proof
    cF
    cG
    cC
    cD
    cful
    co
    #
    wbr
    #
    cF
    cG
    cC
    cD
    cfth
    co
    #
    wbr
    #
    wa
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
    cH
    co
    #
    @5
    cF
    cfv
    @6
    cF
    cfv
    cJ
    co
    #
    @5
    @6
    cG
    co
    #
    wfo
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    #
    @4
    @7
    @8
    @9
    wf1
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    #
    wa
    #
    cF
    cG
    @0
    @2
    cin
    wbr
    @4
    @7
    @8
    @9
    wf1o
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    #
    @1
    @12
    @3
    @15
    vx
    vy
    cB
    cC
    cD
    cF
    cG
    cH
    cJ
    isfth.b
    isfth.j
    isfth.h
    isfull2
    vx
    vy
    cB
    cC
    cD
    cF
    cG
    cH
    cJ
    isfth.b
    isfth.h
    isfth.j
    isfth2
    anbi12i
    cF
    cG
    @0
    @2
    brin
    @19
    @4
    @11
    @14
    wa
    #
    wa
    @16
    @18
    @20
    @4
    @18
    @10
    @13
    wa
    #
    vy
    cB
    wral
    vx
    cB
    wral
    @20
    @17
    @21
    vx
    vy
    cB
    cB
    @17
    @13
    @10
    wa
    @21
    @7
    @8
    @9
    df-f1o
    @13
    @10
    ancom
    bitri
    2ralbii
    @10
    @13
    vx
    vy
    cB
    cB
    r19.26-2
    bitri
    anbi2i
    @4
    @11
    @14
    anandi
    bitri
    3bitr4i
end
