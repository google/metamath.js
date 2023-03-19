include "cr.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cmpt.mm"
include "cvv.mm"
include "a1i.mm"
include "breq1.mm"
include "id.mm"
include "ifbieq2d.mm"
include "ifeq1d.mm"
include "mpteq2dv.mm"
include "adantl.mm"
include "wcel.mm"
include "ovex.mm"
include "mptex.mm"
include "fvmptd.mm"

theorem hoidifhspval
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let vk: setvar k
  let cK: class K
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume hoidifhspval.d: |- D = ( x e. RR |-> ( a e. ( RR ^m X ) |-> ( k e. X |-> if ( k = K , if ( x <_ ( a ` k ) , ( a ` k ) , x ) , ( a ` k ) ) ) ) )
  assume hoidifhspval.y: |- ( ph -> Y e. RR )

  disjoint K x
  disjoint X a
  disjoint X x
  disjoint a x
  disjoint Y a
  disjoint Y x
  disjoint Y k
  disjoint k x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( D ` Y ) = ( a e. ( RR ^m X ) |-> ( k e. X |-> if ( k = K , if ( Y <_ ( a ` k ) , ( a ` k ) , Y ) , ( a ` k ) ) ) ) )

  proof
    wph
    vx
    cY
    va
    cr
    cX
    cmap
    co
    #
    vk
    cX
    vk
    cv
    #
    cK
    wceq
    #
    vx
    cv
    #
    @1
    va
    cv
    cfv
    #
    cle
    wbr
    #
    @4
    @3
    cif
    #
    @4
    cif
    #
    cmpt
    #
    cmpt
    #
    va
    @0
    vk
    cX
    @2
    cY
    @4
    cle
    wbr
    #
    @4
    cY
    cif
    #
    @4
    cif
    #
    cmpt
    #
    cmpt
    #
    cr
    cD
    cvv
    cD
    vx
    cr
    @9
    cmpt
    wceq
    wph
    hoidifhspval.d
    a1i
    @3
    cY
    wceq
    #
    @9
    @14
    wceq
    wph
    @15
    va
    @0
    @8
    @13
    @15
    vk
    cX
    @7
    @12
    @15
    @2
    @6
    @11
    @4
    @15
    @5
    @10
    @3
    cY
    @4
    @3
    cY
    @4
    cle
    breq1
    @15
    id
    ifbieq2d
    ifeq1d
    mpteq2dv
    mpteq2dv
    adantl
    hoidifhspval.y
    @14
    cvv
    wcel
    wph
    va
    @0
    @13
    cr
    cX
    cmap
    ovex
    mptex
    a1i
    fvmptd
end
