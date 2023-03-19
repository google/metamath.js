include "cid.mm"
include "cvv.mm"
include "cv.mm"
include "cmpt.mm"
include "c1.mm"
include "csn.mm"
include "crelexp.mm"
include "co.mm"
include "ciun.mm"
include "dfid4.mm"
include "wcel.mm"
include "1ex.mm"
include "oveq2.mm"
include "iunxsn.mm"
include "relexp1g.mm"
include "syl5eq.mm"
include "mpteq2ia.mm"
include "eqtr4i.mm"

theorem dfid6
  let vx: setvar x
  let vn: setvar n

  disjoint n x
  assert |- _I = ( x e. _V |-> U_ n e. { 1 } ( x ^r n ) )

  proof
    cid
    vx
    cvv
    vx
    cv
    #
    cmpt
    vx
    cvv
    vn
    c1
    csn
    @0
    vn
    cv
    #
    crelexp
    co
    #
    ciun
    #
    cmpt
    vx
    dfid4
    vx
    cvv
    @3
    @0
    @0
    cvv
    wcel
    @3
    @0
    c1
    crelexp
    co
    #
    @0
    vn
    c1
    @2
    @4
    1ex
    @1
    c1
    @0
    crelexp
    oveq2
    iunxsn
    @0
    cvv
    relexp1g
    syl5eq
    mpteq2ia
    eqtr4i
end
