include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cfv.mm"
include "wceq.mm"
include "cif.mm"
include "cvv.mm"
include "eldifi.mm"
include "fvexd.mm"
include "ifexg.mm"
include "syldan.mm"
include "cv.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "ifbieq2d.mm"
include "fvmptg.mm"
include "syl2anr.mm"
include "wn.mm"
include "wne.mm"
include "eldifsn.mm"
include "df-ne.mm"
include "biimpi.mm"
include "adantl.mm"
include "sylbi.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "ex.mm"

theorem symgextfv
  let vx: setvar x
  let cS: class S
  let cE: class E
  let cK: class K
  let cN: class N
  let cX: class X
  let cZ: class Z
  assume symgext.s: |- S = ( Base ` ( SymGrp ` ( N \ { K } ) ) )
  assume symgext.e: |- E = ( x e. N |-> if ( x = K , K , ( Z ` x ) ) )

  disjoint K x
  disjoint N x
  disjoint S x
  disjoint Z x
  disjoint X x
  assert |- ( ( K e. N /\ Z e. S ) -> ( X e. ( N \ { K } ) -> ( E ` X ) = ( Z ` X ) ) )

  proof
    cK
    cN
    wcel
    #
    cZ
    cS
    wcel
    #
    wa
    #
    cX
    cN
    cK
    csn
    #
    cdif
    wcel
    #
    cX
    cE
    cfv
    #
    cX
    cZ
    cfv
    #
    wceq
    @2
    @4
    wa
    #
    @5
    cX
    cK
    wceq
    #
    cK
    @6
    cif
    #
    @6
    @4
    cX
    cN
    wcel
    #
    @9
    cvv
    wcel
    #
    @5
    @9
    wceq
    @2
    cX
    cN
    @3
    eldifi
    @0
    @1
    @6
    cvv
    wcel
    @11
    @2
    cX
    cZ
    fvexd
    @8
    cK
    @6
    cN
    cvv
    ifexg
    syldan
    vx
    cX
    vx
    cv
    #
    cK
    wceq
    #
    cK
    @12
    cZ
    cfv
    #
    cif
    @9
    cN
    cvv
    cE
    @12
    cX
    wceq
    @13
    @8
    @14
    @6
    cK
    @12
    cX
    cK
    eqeq1
    @12
    cX
    cZ
    fveq2
    ifbieq2d
    symgext.e
    fvmptg
    syl2anr
    @7
    @8
    cK
    @6
    @4
    @8
    wn
    #
    @2
    @4
    @10
    cX
    cK
    wne
    #
    wa
    @15
    cX
    cN
    cK
    eldifsn
    @16
    @15
    @10
    @16
    @15
    cX
    cK
    df-ne
    biimpi
    adantl
    sylbi
    adantl
    iffalsed
    eqtrd
    ex
end
