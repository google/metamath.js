include "wcel.mm"
include "cs1.mm"
include "wceq.mm"
include "cword.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cc0.mm"
include "w3a.mm"
include "s1cl.mm"
include "s1len.mm"
include "a1i.mm"
include "s1fv.mm"
include "3jca.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "3anbi123d.mm"
include "syl5ibrcom.mm"
include "wa.mm"
include "eqs1.mm"
include "s1eq.mm"
include "eqeq2d.mm"
include "syl5ibcom.mm"
include "3impia.mm"
include "impbid1.mm"

theorem wrdl1s1
  let cS: class S
  let cV: class V
  let cW: class W


  assert |- ( S e. V -> ( W = <" S "> <-> ( W e. Word V /\ ( # ` W ) = 1 /\ ( W ` 0 ) = S ) ) )

  proof
    cS
    cV
    wcel
    #
    cW
    cS
    cs1
    #
    wceq
    #
    cW
    cV
    cword
    #
    wcel
    #
    cW
    chash
    cfv
    #
    c1
    wceq
    #
    cc0
    cW
    cfv
    #
    cS
    wceq
    #
    w3a
    #
    @0
    @9
    @2
    @1
    @3
    wcel
    #
    @1
    chash
    cfv
    #
    c1
    wceq
    #
    cc0
    @1
    cfv
    #
    cS
    wceq
    #
    w3a
    @0
    @10
    @12
    @14
    cS
    cV
    s1cl
    @12
    @0
    cS
    s1len
    a1i
    cS
    cV
    s1fv
    3jca
    @2
    @4
    @10
    @6
    @12
    @8
    @14
    cW
    @1
    @3
    eleq1
    @2
    @5
    @11
    c1
    cW
    @1
    chash
    fveq2
    eqeq1d
    @2
    @7
    @13
    cS
    cc0
    cW
    @1
    fveq1
    eqeq1d
    3anbi123d
    syl5ibrcom
    @4
    @6
    @8
    @2
    @4
    @6
    wa
    cW
    @7
    cs1
    #
    wceq
    @8
    @2
    cV
    cW
    eqs1
    @8
    @15
    @1
    cW
    @7
    cS
    s1eq
    eqeq2d
    syl5ibcom
    3impia
    impbid1
end
