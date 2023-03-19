include "wcel.mm"
include "cclwlks.mm"
include "cfv.mm"
include "c1st.mm"
include "chash.mm"
include "wceq.mm"
include "cv.mm"
include "fveq2i.mm"
include "eqeq1i.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "syl5bb.mm"
include "elrab2.mm"
include "simprbi.mm"

theorem clwlksfclwwlk1hashn
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cN: class N
  let cW: class W
  let vc: setvar c
  let vi: setvar i
  assume clwlksfclwwlk.1: |- A = ( 1st ` c )
  assume clwlksfclwwlk.2: |- B = ( 2nd ` c )
  assume clwlksfclwwlk.c: |- C = { c e. ( ClWalks ` G ) | ( # ` A ) = N }
  assume clwlksfclwwlk.f: |- F = ( c e. C |-> ( B substr <. 0 , ( # ` A ) >. ) )

  disjoint G c
  disjoint N c
  disjoint W c
  disjoint A i
  disjoint B i
  disjoint G i
  disjoint c i
  assert |- ( W e. C -> ( # ` ( 1st ` W ) ) = N )

  proof
    cW
    cC
    wcel
    cW
    cG
    cclwlks
    cfv
    #
    wcel
    cW
    c1st
    cfv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    cA
    chash
    cfv
    #
    cN
    wceq
    #
    @3
    vc
    cW
    @0
    cC
    @5
    vc
    cv
    #
    c1st
    cfv
    #
    chash
    cfv
    #
    cN
    wceq
    @6
    cW
    wceq
    #
    @3
    @4
    @8
    cN
    cA
    @7
    chash
    clwlksfclwwlk.1
    fveq2i
    eqeq1i
    @9
    @8
    @2
    cN
    @9
    @7
    @1
    chash
    @6
    cW
    c1st
    fveq2
    fveq2d
    eqeq1d
    syl5bb
    clwlksfclwwlk.c
    elrab2
    simprbi
end
