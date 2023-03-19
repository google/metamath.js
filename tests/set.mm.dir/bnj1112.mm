include "cv.mm"
include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "wa.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "bnj115.mm"
include "eleq1.mm"
include "suceq.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "bnj1113.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "cbvalv.mm"
include "bitri.mm"

theorem bnj1112
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  assume bnj1112.1: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )

  disjoint A i
  disjoint A j
  disjoint i j
  disjoint R i
  disjoint R j
  disjoint f i
  disjoint f j
  disjoint f y
  disjoint i y
  disjoint j y
  disjoint i n
  disjoint j n
  assert |- ( ps <-> A. j ( ( j e. _om /\ suc j e. n ) -> ( f ` suc j ) = U_ y e. ( f ` j ) _pred ( y , A , R ) ) )

  proof
    wps
    vi
    cv
    #
    com
    wcel
    #
    @0
    csuc
    #
    vn
    cv
    #
    wcel
    #
    wa
    #
    @2
    vf
    cv
    #
    cfv
    #
    vy
    @0
    @6
    cfv
    #
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
    wi
    #
    vi
    wal
    vj
    cv
    #
    com
    wcel
    #
    @13
    csuc
    #
    @3
    wcel
    #
    wa
    #
    @15
    @6
    cfv
    #
    vy
    @13
    @6
    cfv
    #
    @9
    ciun
    #
    wceq
    #
    wi
    #
    vj
    wal
    @11
    @4
    wps
    com
    vi
    bnj1112.1
    bnj115
    @12
    @22
    vi
    vj
    @0
    @13
    wceq
    #
    @5
    @17
    @11
    @21
    @23
    @1
    @14
    @4
    @16
    @0
    @13
    com
    eleq1
    @23
    @2
    @15
    @3
    @0
    @13
    suceq
    #
    eleq1d
    anbi12d
    @23
    @7
    @18
    @10
    @20
    @23
    @2
    @15
    @6
    @24
    fveq2d
    vy
    @0
    @13
    @8
    @19
    @9
    @0
    @13
    @6
    fveq2
    bnj1113
    eqeq12d
    imbi12d
    cbvalv
    bitri
end
