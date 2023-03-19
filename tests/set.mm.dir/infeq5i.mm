include "com.mm"
include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "wpss.mm"
include "cv.mm"
include "wex.mm"
include "difexg.mm"
include "0ex.mm"
include "snid.mm"
include "wn.mm"
include "wceq.mm"
include "cin.mm"
include "disj4.mm"
include "disj3.mm"
include "bitr3i.mm"
include "peano1.mm"
include "eleq2.mm"
include "mpbii.mm"
include "eldifbd.mm"
include "sylbi.mm"
include "mt4.mm"
include "unidif0.mm"
include "wlim.mm"
include "limom.mm"
include "limuni.mm"
include "ax-mp.mm"
include "eqtr4i.mm"
include "psseq2i.mm"
include "mpbir.mm"
include "psseq1.mm"
include "unieq.mm"
include "psseq2d.mm"
include "bitrd.mm"
include "spcegv.mm"
include "mpisyl.mm"

theorem infeq5i
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w


  assert |- ( _om e. _V -> E. x x C. U. x )

  proof
    com
    cvv
    wcel
    com
    c0
    csn
    #
    cdif
    #
    cvv
    wcel
    @1
    @1
    cuni
    #
    wpss
    #
    vx
    cv
    #
    @4
    cuni
    #
    wpss
    #
    vx
    wex
    com
    @0
    cvv
    difexg
    @3
    @1
    com
    wpss
    #
    c0
    @0
    wcel
    #
    @7
    c0
    0ex
    snid
    @7
    wn
    #
    com
    @1
    wceq
    #
    @8
    wn
    @9
    com
    @0
    cin
    c0
    wceq
    @10
    com
    @0
    disj4
    com
    @0
    disj3
    bitr3i
    @10
    c0
    com
    @0
    @10
    c0
    com
    wcel
    c0
    @1
    wcel
    peano1
    com
    @1
    c0
    eleq2
    mpbii
    eldifbd
    sylbi
    mt4
    @2
    com
    @1
    @2
    com
    cuni
    #
    com
    com
    unidif0
    com
    wlim
    com
    @11
    wceq
    limom
    com
    limuni
    ax-mp
    eqtr4i
    psseq2i
    mpbir
    @6
    @3
    vx
    @1
    cvv
    @4
    @1
    wceq
    #
    @6
    @1
    @5
    wpss
    @3
    @4
    @1
    @5
    psseq1
    @12
    @5
    @2
    @1
    @4
    @1
    unieq
    psseq2d
    bitrd
    spcegv
    mpisyl
end
