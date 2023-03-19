include "c2o.mm"
include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wrex.mm"
include "cfv.mm"
include "elxp2.mm"
include "wa.mm"
include "co.mm"
include "c1o.mm"
include "cdif.mm"
include "efgmval.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "2oconcl.mm"
include "sylan2.mm"
include "wss.mm"
include "csuc.mm"
include "word.mm"
include "wtr.mm"
include "wi.mm"
include "1on.mm"
include "onordi.mm"
include "ordtr.mm"
include "trsucss.mm"
include "mp2b.mm"
include "df-2o.mm"
include "eleq2s.mm"
include "adantl.mm"
include "dfss4.mm"
include "sylib.mm"
include "opeq2d.mm"
include "3eqtrd.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "sylbi.mm"

theorem efgmnvl
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cI: class I
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let cB: class B
  assume efgmval.m: |- M = ( y e. I , z e. 2o |-> <. y , ( 1o \ z ) >. )

  disjoint y z
  disjoint I y
  disjoint I z
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  disjoint a y
  disjoint a z
  disjoint I a
  disjoint b y
  disjoint b z
  disjoint I b
  disjoint M a
  disjoint M b
  assert |- ( A e. ( I X. 2o ) -> ( M ` ( M ` A ) ) = A )

  proof
    cA
    cI
    c2o
    cxp
    wcel
    cA
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    wceq
    #
    vb
    c2o
    wrex
    va
    cI
    wrex
    cA
    cM
    cfv
    #
    cM
    cfv
    #
    cA
    wceq
    #
    va
    vb
    cA
    cI
    c2o
    elxp2
    @3
    @6
    va
    vb
    cI
    c2o
    @0
    cI
    wcel
    #
    @1
    c2o
    wcel
    #
    wa
    #
    @6
    @3
    @0
    @1
    cM
    co
    #
    cM
    cfv
    #
    @2
    wceq
    @9
    @11
    @0
    c1o
    @1
    cdif
    #
    cM
    co
    #
    @0
    c1o
    @12
    cdif
    #
    cop
    #
    @2
    @9
    @11
    @0
    @12
    cop
    #
    cM
    cfv
    @13
    @9
    @10
    @16
    cM
    vy
    vz
    @0
    @1
    cI
    cM
    efgmval.m
    efgmval
    fveq2d
    @0
    @12
    cM
    df-ov
    syl6eqr
    @8
    @7
    @12
    c2o
    wcel
    @13
    @15
    wceq
    @1
    2oconcl
    vy
    vz
    @0
    @12
    cI
    cM
    efgmval.m
    efgmval
    sylan2
    @9
    @14
    @1
    @0
    @9
    @1
    c1o
    wss
    #
    @14
    @1
    wceq
    @8
    @17
    @7
    @17
    @1
    c1o
    csuc
    #
    c2o
    c1o
    word
    c1o
    wtr
    @1
    @18
    wcel
    @17
    wi
    c1o
    1on
    onordi
    c1o
    ordtr
    c1o
    @1
    trsucss
    mp2b
    df-2o
    eleq2s
    adantl
    @1
    c1o
    dfss4
    sylib
    opeq2d
    3eqtrd
    @3
    @5
    @11
    cA
    @2
    @3
    @4
    @10
    cM
    @3
    @4
    @2
    cM
    cfv
    @10
    cA
    @2
    cM
    fveq2
    @0
    @1
    cM
    df-ov
    syl6eqr
    fveq2d
    @3
    id
    eqeq12d
    syl5ibrcom
    rexlimivv
    sylbi
end
