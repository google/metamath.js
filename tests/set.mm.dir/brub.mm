include "cvv.mm"
include "cxp.mm"
include "cdif.mm"
include "cep.mm"
include "ccnv.mm"
include "ccom.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "wn.mm"
include "cub.mm"
include "wral.mm"
include "wcel.mm"
include "brxp.mm"
include "mpbir2an.mm"
include "brdif.mm"
include "mpbiran.mm"
include "coepr.mm"
include "xchbinx.mm"
include "df-ub.mm"
include "breqi.mm"
include "brv.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "con2bii.mm"
include "3bitr4i.mm"

theorem brub
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cS: class S
  assume brub.1: |- S e. _V
  assume brub.2: |- A e. _V

  disjoint A x
  disjoint R x
  disjoint S x
  assert |- ( S UB R A <-> A. x e. S x R A )

  proof
    cS
    cA
    cvv
    cvv
    cxp
    #
    cvv
    cR
    cdif
    #
    cep
    ccnv
    ccom
    #
    cdif
    #
    wbr
    #
    vx
    cv
    #
    cA
    @1
    wbr
    #
    vx
    cS
    wrex
    #
    wn
    cS
    cA
    cR
    cub
    #
    wbr
    @5
    cA
    cR
    wbr
    #
    vx
    cS
    wral
    #
    @4
    cS
    cA
    @2
    wbr
    #
    @7
    @4
    cS
    cA
    @0
    wbr
    #
    @11
    wn
    @12
    cS
    cvv
    wcel
    cA
    cvv
    wcel
    brub.1
    brub.2
    cS
    cA
    cvv
    cvv
    brxp
    mpbir2an
    cS
    cA
    @0
    @2
    brdif
    mpbiran
    vx
    cS
    cA
    @1
    brub.1
    brub.2
    coepr
    xchbinx
    cS
    cA
    @8
    @3
    cR
    df-ub
    breqi
    @7
    @10
    @7
    @9
    wn
    #
    vx
    cS
    wrex
    @10
    wn
    @6
    @13
    vx
    cS
    @6
    @5
    cA
    cvv
    wbr
    @13
    @5
    cA
    brv
    @5
    cA
    cvv
    cR
    brdif
    mpbiran
    rexbii
    @9
    vx
    cS
    rexnal
    bitri
    con2bii
    3bitr4i
end
