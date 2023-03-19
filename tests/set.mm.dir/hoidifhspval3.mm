include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cvv.mm"
include "hoidifhspval2.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "breq2d.mm"
include "ifbieq1d.mm"
include "ifbieq12d.mm"
include "adantl.mm"
include "fvexd.mm"
include "cr.mm"
include "elexd.mm"
include "ifcld.mm"
include "fvmptd.mm"

theorem hoidifhspval3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cD: class D
  let vk: setvar k
  let cJ: class J
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume hoidifhspval3.d: |- D = ( x e. RR |-> ( a e. ( RR ^m X ) |-> ( k e. X |-> if ( k = K , if ( x <_ ( a ` k ) , ( a ` k ) , x ) , ( a ` k ) ) ) ) )
  assume hoidifhspval3.y: |- ( ph -> Y e. RR )
  assume hoidifhspval3.x: |- ( ph -> X e. V )
  assume hoidifhspval3.a: |- ( ph -> A : X --> RR )
  assume hoidifhspval3.j: |- ( ph -> J e. X )

  disjoint A a
  disjoint A k
  disjoint a k
  disjoint J k
  disjoint K a
  disjoint K k
  disjoint K x
  disjoint a x
  disjoint k x
  disjoint X a
  disjoint X k
  disjoint X x
  disjoint Y a
  disjoint Y k
  disjoint Y x
  disjoint a ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( ( D ` Y ) ` A ) ` J ) = if ( J = K , if ( Y <_ ( A ` J ) , ( A ` J ) , Y ) , ( A ` J ) ) )

  proof
    wph
    vk
    cJ
    vk
    cv
    #
    cK
    wceq
    #
    cY
    @0
    cA
    cfv
    #
    cle
    wbr
    #
    @2
    cY
    cif
    #
    @2
    cif
    #
    cJ
    cK
    wceq
    #
    cY
    cJ
    cA
    cfv
    #
    cle
    wbr
    #
    @7
    cY
    cif
    #
    @7
    cif
    #
    cX
    cA
    cY
    cD
    cfv
    cfv
    cvv
    wph
    vx
    cA
    cD
    vk
    cK
    cV
    cX
    cY
    va
    hoidifhspval3.d
    hoidifhspval3.y
    hoidifhspval3.x
    hoidifhspval3.a
    hoidifhspval2
    @0
    cJ
    wceq
    #
    @5
    @10
    wceq
    wph
    @11
    @1
    @6
    @4
    @2
    @9
    @7
    @0
    cJ
    cK
    eqeq1
    @11
    @3
    @8
    @2
    @7
    cY
    @11
    @2
    @7
    cY
    cle
    @0
    cJ
    cA
    fveq2
    #
    breq2d
    @12
    ifbieq1d
    @12
    ifbieq12d
    adantl
    hoidifhspval3.j
    wph
    @6
    @9
    @7
    cvv
    wph
    @8
    @7
    cY
    cvv
    wph
    cJ
    cA
    fvexd
    #
    wph
    cY
    cr
    hoidifhspval3.y
    elexd
    ifcld
    @13
    ifcld
    fvmptd
end
