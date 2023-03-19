include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wb.mm"
include "wal.mm"
include "cvv.mm"
include "cep.mm"
include "ctxp.mm"
include "csymdif.mm"
include "crn.mm"
include "cop.mm"
include "wn.mm"
include "wex.mm"
include "df-br.mm"
include "opex.mm"
include "elrn.mm"
include "brsymdif.mm"
include "brv.mm"
include "vex.mm"
include "brtxp.mm"
include "mpbiran.mm"
include "epelc.mm"
include "bitri.mm"
include "mpbiran2.mm"
include "bibi12i.mm"
include "xchbinx.mm"
include "exbii.mm"
include "exnal.mm"
include "3bitrri.mm"
include "con1bii.mm"

theorem brtxpsd
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  assume brtxpsd.1: |- A e. _V
  assume brtxpsd.2: |- B e. _V

  disjoint A x
  disjoint B x
  disjoint R x
  assert |- ( -. A ran ( ( _V (x) _E ) /_\ ( R (x) _V ) ) B <-> A. x ( x e. B <-> x R A ) )

  proof
    vx
    cv
    #
    cB
    wcel
    #
    @0
    cA
    cR
    wbr
    #
    wb
    #
    vx
    wal
    #
    cA
    cB
    cvv
    cep
    ctxp
    #
    cR
    cvv
    ctxp
    #
    csymdif
    #
    crn
    #
    wbr
    #
    @9
    cA
    cB
    cop
    #
    @8
    wcel
    #
    @3
    wn
    #
    vx
    wex
    #
    @4
    wn
    cA
    cB
    @8
    df-br
    @11
    @0
    @10
    @7
    wbr
    #
    vx
    wex
    @13
    vx
    @10
    @7
    cA
    cB
    opex
    elrn
    @14
    @12
    vx
    @14
    @0
    @10
    @5
    wbr
    #
    @0
    @10
    @6
    wbr
    #
    wb
    @3
    @0
    @10
    @5
    @6
    brsymdif
    @15
    @1
    @16
    @2
    @15
    @0
    cB
    cep
    wbr
    #
    @1
    @15
    @0
    cA
    cvv
    wbr
    @17
    @0
    cA
    brv
    cvv
    cep
    @0
    cA
    cB
    vx
    vex
    #
    brtxpsd.1
    brtxpsd.2
    brtxp
    mpbiran
    @0
    cB
    brtxpsd.2
    epelc
    bitri
    @16
    @2
    @0
    cB
    cvv
    wbr
    @0
    cB
    brv
    cR
    cvv
    @0
    cA
    cB
    @18
    brtxpsd.1
    brtxpsd.2
    brtxp
    mpbiran2
    bibi12i
    xchbinx
    exbii
    bitri
    @3
    vx
    exnal
    3bitrri
    con1bii
end
