include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "c1.mm"
include "cneg.mm"
include "cexp.mm"
include "even2n.mm"
include "wcel.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "m1expeven.mm"
include "sylan9eqr.mm"
include "rexlimiva.mm"
include "sylbi.mm"

theorem m1expe
  let cN: class N
  let vn: setvar n


  assert |- ( 2 || N -> ( -u 1 ^ N ) = 1 )

  proof
    c2
    cN
    cdvds
    wbr
    c2
    vn
    cv
    #
    cmul
    co
    #
    cN
    wceq
    #
    vn
    cz
    wrex
    c1
    cneg
    #
    cN
    cexp
    co
    #
    c1
    wceq
    #
    vn
    cN
    even2n
    @2
    @5
    vn
    cz
    @2
    @0
    cz
    wcel
    @4
    @3
    @1
    cexp
    co
    #
    c1
    @4
    @6
    wceq
    cN
    @1
    cN
    @1
    @3
    cexp
    oveq2
    eqcoms
    @0
    m1expeven
    sylan9eqr
    rexlimiva
    sylbi
end
