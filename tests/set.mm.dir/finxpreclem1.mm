include "wcel.mm"
include "c1o.mm"
include "cop.mm"
include "com.mm"
include "cvv.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "cxp.mm"
include "cuni.mm"
include "c1st.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt2.mm"
include "co.mm"
include "df-ov.mm"
include "eqidd.mm"
include "eleq1a.mm"
include "anim2d.mm"
include "iftrue.mm"
include "syl6.mm"
include "imp.mm"
include "1onn.mm"
include "a1i.mm"
include "elex.mm"
include "0ex.mm"
include "ovmpt2d.mm"
include "syl5reqr.mm"

theorem finxpreclem1
  let vx: setvar x
  let cU: class U
  let vn: setvar n
  let cX: class X

  disjoint U n
  disjoint U x
  disjoint n x
  disjoint X n
  disjoint X x
  assert |- ( X e. U -> (/) = ( ( n e. _om , x e. _V |-> if ( ( n = 1o /\ x e. U ) , (/) , if ( x e. ( _V X. U ) , <. U. n , ( 1st ` x ) >. , <. n , x >. ) ) ) ` <. 1o , X >. ) )

  proof
    cX
    cU
    wcel
    #
    c1o
    cX
    cop
    vn
    vx
    com
    cvv
    vn
    cv
    #
    c1o
    wceq
    #
    vx
    cv
    #
    cU
    wcel
    #
    wa
    #
    c0
    @3
    cvv
    cU
    cxp
    wcel
    @1
    cuni
    @3
    c1st
    cfv
    cop
    @1
    @3
    cop
    cif
    #
    cif
    #
    cmpt2
    #
    cfv
    c1o
    cX
    @8
    co
    c0
    c1o
    cX
    @8
    df-ov
    @0
    vn
    vx
    c1o
    cX
    com
    cvv
    @7
    c0
    @8
    cvv
    @0
    @8
    eqidd
    @0
    @2
    @3
    cX
    wceq
    #
    wa
    #
    @7
    c0
    wceq
    #
    @0
    @10
    @5
    @11
    @0
    @9
    @4
    @2
    cX
    cU
    @3
    eleq1a
    anim2d
    @5
    c0
    @6
    iftrue
    syl6
    imp
    c1o
    com
    wcel
    @0
    1onn
    a1i
    cX
    cU
    elex
    c0
    cvv
    wcel
    @0
    0ex
    a1i
    ovmpt2d
    syl5reqr
end
