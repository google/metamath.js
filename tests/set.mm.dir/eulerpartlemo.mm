include "c2.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "wral.mm"
include "wceq.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "raleqdv.mm"
include "elrab2.mm"

theorem eulerpartlemo
  let cA: class A
  let cD: class D
  let cP: class P
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let cN: class N
  let cO: class O
  assume eulerpart.p: |- P = { f e. ( NN0 ^m NN ) | ( ( `' f " NN ) e. Fin /\ sum_ k e. NN ( ( f ` k ) x. k ) = N ) }
  assume eulerpart.o: |- O = { g e. P | A. n e. ( `' g " NN ) -. 2 || n }
  assume eulerpart.d: |- D = { g e. P | A. n e. NN ( g ` n ) <_ 1 }

  disjoint g n
  disjoint A g
  disjoint A n
  disjoint P g
  assert |- ( A e. O <-> ( A e. P /\ A. n e. ( `' A " NN ) -. 2 || n ) )

  proof
    c2
    vn
    cv
    cdvds
    wbr
    wn
    #
    vn
    vg
    cv
    #
    ccnv
    #
    cn
    cima
    #
    wral
    @0
    vn
    cA
    ccnv
    #
    cn
    cima
    #
    wral
    vg
    cA
    cP
    cO
    @1
    cA
    wceq
    #
    @0
    vn
    @3
    @5
    @6
    @2
    @4
    cn
    @1
    cA
    cnveq
    imaeq1d
    raleqdv
    eulerpart.o
    elrab2
end
