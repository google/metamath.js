include "co.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "elmpt2cl.mm"
include "cvv.mm"
include "wceq.mm"
include "wal.mm"
include "gen2.mm"
include "cv.mm"
include "eleq1d.mm"
include "spc2gv.mm"
include "mpi.mm"
include "ovmpt2ga.mm"
include "mpd3an3.mm"
include "eleq2d.mm"
include "biadan2.mm"
include "df-3an.mm"
include "bitr4i.mm"

theorem elovmpt2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  assume elovmpt2.d: |- D = ( a e. A , b e. B |-> C )
  assume elovmpt2.c: |- C e. _V
  assume elovmpt2.e: |- ( ( a = X /\ b = Y ) -> C = E )

  disjoint A a
  disjoint A b
  disjoint a b
  disjoint B a
  disjoint B b
  disjoint E a
  disjoint E b
  disjoint F a
  disjoint F b
  disjoint X a
  disjoint X b
  disjoint Y a
  disjoint Y b
  assert |- ( F e. ( X D Y ) <-> ( X e. A /\ Y e. B /\ F e. E ) )

  proof
    cF
    cX
    cY
    cD
    co
    #
    wcel
    #
    cX
    cA
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cF
    cE
    wcel
    #
    wa
    @2
    @3
    @5
    w3a
    @1
    @4
    @5
    va
    vb
    cA
    cB
    cC
    cX
    cY
    cD
    cF
    elovmpt2.d
    elmpt2cl
    @4
    @0
    cE
    cF
    @2
    @3
    cE
    cvv
    wcel
    #
    @0
    cE
    wceq
    @4
    cC
    cvv
    wcel
    #
    vb
    wal
    va
    wal
    @6
    @7
    va
    vb
    elovmpt2.c
    gen2
    @7
    @6
    va
    vb
    cX
    cY
    cA
    cB
    va
    cv
    cX
    wceq
    vb
    cv
    cY
    wceq
    wa
    cC
    cE
    cvv
    elovmpt2.e
    eleq1d
    spc2gv
    mpi
    va
    vb
    cX
    cY
    cA
    cB
    cC
    cE
    cD
    cvv
    elovmpt2.e
    elovmpt2.d
    ovmpt2ga
    mpd3an3
    eleq2d
    biadan2
    @2
    @3
    @5
    df-3an
    bitr4i
end
