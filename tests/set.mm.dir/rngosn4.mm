include "crngo.mm"
include "wcel.mm"
include "wa.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "csn.mm"
include "wceq.mm"
include "cop.mm"
include "wb.mm"
include "en1eqsnbi.mm"
include "adantl.mm"
include "rngosn3.mm"
include "bitrd.mm"

theorem rngosn4
  let cA: class A
  let cR: class R
  let cG: class G
  let cX: class X
  assume on1el3.1: |- G = ( 1st ` R )
  assume on1el3.2: |- X = ran G


  assert |- ( ( R e. RingOps /\ A e. X ) -> ( X ~~ 1o <-> R = <. { <. <. A , A >. , A >. } , { <. <. A , A >. , A >. } >. ) )

  proof
    cR
    crngo
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    cX
    c1o
    cen
    wbr
    #
    cX
    cA
    csn
    wceq
    #
    cR
    cA
    cA
    cop
    cA
    cop
    csn
    #
    @4
    cop
    wceq
    @1
    @2
    @3
    wb
    @0
    cA
    cX
    en1eqsnbi
    adantl
    cA
    cX
    cR
    cG
    cX
    on1el3.1
    on1el3.2
    rngosn3
    bitrd
end
