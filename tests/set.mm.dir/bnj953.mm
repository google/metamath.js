include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "csuc.mm"
include "com.mm"
include "wcel.mm"
include "wa.mm"
include "w-bnj17.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "bnj312.mm"
include "bnj251.mm"
include "bitri.mm"
include "wi.mm"
include "wal.mm"
include "bnj115.mm"
include "sp.mm"
include "impcom.mm"
include "sylan2b.mm"
include "bnj956.mm"
include "eqtr3.mm"
include "syl2anr.mm"
include "eqtr.mm"
include "sylan2.mm"
include "sylbi.mm"

theorem bnj953
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cG: class G
  assume bnj953.1: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj953.2: |- ( ( G ` i ) = ( f ` i ) -> A. y ( G ` i ) = ( f ` i ) )


  assert |- ( ( ( G ` i ) = ( f ` i ) /\ ( G ` suc i ) = ( f ` suc i ) /\ ( i e. _om /\ suc i e. n ) /\ ps ) -> ( G ` suc i ) = U_ y e. ( G ` i ) _pred ( y , A , R ) )

  proof
    vi
    cv
    #
    cG
    cfv
    #
    @0
    vf
    cv
    #
    cfv
    #
    wceq
    #
    @0
    csuc
    #
    cG
    cfv
    #
    @5
    @2
    cfv
    #
    wceq
    #
    @0
    com
    wcel
    @5
    vn
    cv
    wcel
    #
    wa
    #
    wps
    w-bnj17
    #
    @8
    @4
    @10
    wps
    wa
    #
    wa
    #
    wa
    #
    @6
    vy
    @1
    cA
    cR
    vy
    cv
    c-bnj14
    #
    ciun
    #
    wceq
    #
    @11
    @8
    @4
    @10
    wps
    w-bnj17
    @14
    @4
    @8
    @10
    wps
    bnj312
    @8
    @4
    @10
    wps
    bnj251
    bitri
    @13
    @8
    @7
    @16
    wceq
    #
    @17
    @12
    @7
    vy
    @3
    @15
    ciun
    #
    wceq
    #
    @16
    @19
    wceq
    @18
    @4
    wps
    @10
    @10
    @20
    wi
    #
    vi
    wal
    #
    @20
    @20
    @9
    wps
    com
    vi
    bnj953.1
    bnj115
    @22
    @10
    @20
    @21
    vi
    sp
    impcom
    sylan2b
    vy
    @1
    @3
    @15
    bnj953.2
    bnj956
    @7
    @16
    @19
    eqtr3
    syl2anr
    @6
    @7
    @16
    eqtr
    sylan2
    sylbi
end
