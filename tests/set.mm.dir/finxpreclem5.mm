include "cv.mm"
include "com.mm"
include "wcel.mm"
include "c1o.mm"
include "wa.mm"
include "cvv.mm"
include "cxp.mm"
include "wn.mm"
include "cop.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "df-ov.mm"
include "c0.mm"
include "cuni.mm"
include "c1st.mm"
include "cif.mm"
include "vex.mm"
include "0ex.mm"
include "opex.mm"
include "ifex.mm"
include "ovmpt4g.mm"
include "mp3an23.mm"
include "ad2antrr.mm"
include "1on.mm"
include "onirri.mm"
include "eleq2.mm"
include "mtbiri.mm"
include "con2i.mm"
include "intnanrd.mm"
include "iffalsed.mm"
include "adantl.mm"
include "iffalse.mm"
include "sylan9eq.mm"
include "eqtrd.mm"
include "syl5eqr.mm"
include "ex.mm"

theorem finxpreclem5
  let vx: setvar x
  let cU: class U
  let vn: setvar n
  let cF: class F
  assume finxpreclem5.1: |- F = ( n e. _om , x e. _V |-> if ( ( n = 1o /\ x e. U ) , (/) , if ( x e. ( _V X. U ) , <. U. n , ( 1st ` x ) >. , <. n , x >. ) ) )

  disjoint n x
  assert |- ( ( n e. _om /\ 1o e. n ) -> ( -. x e. ( _V X. U ) -> ( F ` <. n , x >. ) = <. n , x >. ) )

  proof
    vn
    cv
    #
    com
    wcel
    #
    c1o
    @0
    wcel
    #
    wa
    #
    vx
    cv
    #
    cvv
    cU
    cxp
    wcel
    #
    wn
    #
    @0
    @4
    cop
    #
    cF
    cfv
    #
    @7
    wceq
    @3
    @6
    wa
    #
    @8
    @0
    @4
    cF
    co
    #
    @7
    @0
    @4
    cF
    df-ov
    @9
    @10
    @0
    c1o
    wceq
    #
    @4
    cU
    wcel
    #
    wa
    #
    c0
    @5
    @0
    cuni
    #
    @4
    c1st
    cfv
    #
    cop
    #
    @7
    cif
    #
    cif
    #
    @7
    @1
    @10
    @18
    wceq
    #
    @2
    @6
    @1
    @4
    cvv
    wcel
    @18
    cvv
    wcel
    @19
    vx
    vex
    @13
    c0
    @17
    0ex
    @5
    @16
    @7
    @14
    @15
    opex
    @0
    @4
    opex
    ifex
    ifex
    vn
    vx
    com
    cvv
    @18
    cF
    cvv
    finxpreclem5.1
    ovmpt4g
    mp3an23
    ad2antrr
    @3
    @6
    @18
    @17
    @7
    @2
    @18
    @17
    wceq
    @1
    @2
    @13
    c0
    @17
    @2
    @11
    @12
    @11
    @2
    @11
    @2
    c1o
    c1o
    wcel
    c1o
    1on
    onirri
    @0
    c1o
    c1o
    eleq2
    mtbiri
    con2i
    intnanrd
    iffalsed
    adantl
    @5
    @16
    @7
    iffalse
    sylan9eq
    eqtrd
    syl5eqr
    ex
end
