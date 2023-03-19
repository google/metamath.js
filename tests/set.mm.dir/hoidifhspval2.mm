include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cmpt.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "cvv.mm"
include "hoidifhspval.mm"
include "fveq1.mm"
include "breq2d.mm"
include "ifbieq1d.mm"
include "ifeq12d.mm"
include "mpteq2dv.mm"
include "adantl.mm"
include "wcel.mm"
include "wf.mm"
include "wa.mm"
include "wb.mm"
include "reex.mm"
include "a1i.mm"
include "jca.mm"
include "elmapg.mm"
include "syl.mm"
include "mpbird.mm"
include "mptexg.mm"
include "fvmptd.mm"

theorem hoidifhspval2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cD: class D
  let vk: setvar k
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume hoidifhspval2.d: |- D = ( x e. RR |-> ( a e. ( RR ^m X ) |-> ( k e. X |-> if ( k = K , if ( x <_ ( a ` k ) , ( a ` k ) , x ) , ( a ` k ) ) ) ) )
  assume hoidifhspval2.y: |- ( ph -> Y e. RR )
  assume hoidifhspval2.x: |- ( ph -> X e. V )
  assume hoidifhspval2.a: |- ( ph -> A : X --> RR )

  disjoint A a
  disjoint A k
  disjoint a k
  disjoint K a
  disjoint K x
  disjoint a x
  disjoint X a
  disjoint X k
  disjoint X x
  disjoint k x
  disjoint Y a
  disjoint Y k
  disjoint Y x
  disjoint a ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( D ` Y ) ` A ) = ( k e. X |-> if ( k = K , if ( Y <_ ( A ` k ) , ( A ` k ) , Y ) , ( A ` k ) ) ) )

  proof
    wph
    va
    cA
    vk
    cX
    vk
    cv
    #
    cK
    wceq
    #
    cY
    @0
    va
    cv
    #
    cfv
    #
    cle
    wbr
    #
    @3
    cY
    cif
    #
    @3
    cif
    #
    cmpt
    #
    vk
    cX
    @1
    cY
    @0
    cA
    cfv
    #
    cle
    wbr
    #
    @8
    cY
    cif
    #
    @8
    cif
    #
    cmpt
    #
    cr
    cX
    cmap
    co
    #
    cY
    cD
    cfv
    cvv
    wph
    vx
    cD
    vk
    cK
    cX
    cY
    va
    hoidifhspval2.d
    hoidifhspval2.y
    hoidifhspval
    @2
    cA
    wceq
    #
    @7
    @12
    wceq
    wph
    @14
    vk
    cX
    @6
    @11
    @14
    @1
    @5
    @10
    @3
    @8
    @14
    @4
    @9
    @3
    @8
    cY
    @14
    @3
    @8
    cY
    cle
    @0
    @2
    cA
    fveq1
    #
    breq2d
    @15
    ifbieq1d
    @15
    ifeq12d
    mpteq2dv
    adantl
    wph
    cA
    @13
    wcel
    #
    cX
    cr
    cA
    wf
    #
    hoidifhspval2.a
    wph
    cr
    cvv
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    @16
    @17
    wb
    wph
    @18
    @19
    @18
    wph
    reex
    a1i
    hoidifhspval2.x
    jca
    cr
    cX
    cA
    cvv
    cV
    elmapg
    syl
    mpbird
    wph
    @19
    @12
    cvv
    wcel
    hoidifhspval2.x
    vk
    cX
    @11
    cV
    mptexg
    syl
    fvmptd
end
