include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "ccnv.mm"
include "cima.mm"
include "wss.mm"
include "cvv.mm"
include "cfn.mm"
include "cin.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "sseq1d.mm"
include "elrab2.mm"
include "eleq1d.mm"
include "elab4g.mm"
include "anbi12i.mm"
include "elin.mm"
include "elex.mm"
include "pm4.71i.mm"
include "anbi1i.mm"
include "3anass.mm"
include "an42.mm"
include "3bitr4i.mm"

theorem eulerpartlemt0
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let vr: setvar r
  assume eulerpart.p: |- P = { f e. ( NN0 ^m NN ) | ( ( `' f " NN ) e. Fin /\ sum_ k e. NN ( ( f ` k ) x. k ) = N ) }
  assume eulerpart.o: |- O = { g e. P | A. n e. ( `' g " NN ) -. 2 || n }
  assume eulerpart.d: |- D = { g e. P | A. n e. NN ( g ` n ) <_ 1 }
  assume eulerpart.j: |- J = { z e. NN | -. 2 || z }
  assume eulerpart.f: |- F = ( x e. J , y e. NN0 |-> ( ( 2 ^ y ) x. x ) )
  assume eulerpart.h: |- H = { r e. ( ( ~P NN0 i^i Fin ) ^m J ) | ( r supp (/) ) e. Fin }
  assume eulerpart.m: |- M = ( r e. H |-> { <. x , y >. | ( x e. J /\ y e. ( r ` x ) ) } )
  assume eulerpart.r: |- R = { f | ( `' f " NN ) e. Fin }
  assume eulerpart.t: |- T = { f e. ( NN0 ^m NN ) | ( `' f " NN ) C_ J }

  disjoint A f
  disjoint J f
  assert |- ( A e. ( T i^i R ) <-> ( A e. ( NN0 ^m NN ) /\ ( `' A " NN ) e. Fin /\ ( `' A " NN ) C_ J ) )

  proof
    cA
    cT
    wcel
    #
    cA
    cR
    wcel
    #
    wa
    cA
    cn0
    cn
    cmap
    co
    #
    wcel
    #
    cA
    ccnv
    #
    cn
    cima
    #
    cJ
    wss
    #
    wa
    #
    cA
    cvv
    wcel
    #
    @5
    cfn
    wcel
    #
    wa
    #
    wa
    #
    cA
    cT
    cR
    cin
    wcel
    @3
    @9
    @6
    w3a
    #
    @0
    @7
    @1
    @10
    vf
    cv
    #
    ccnv
    #
    cn
    cima
    #
    cJ
    wss
    @6
    vf
    cA
    @2
    cT
    @13
    cA
    wceq
    #
    @15
    @5
    cJ
    @16
    @14
    @4
    cn
    @13
    cA
    cnveq
    imaeq1d
    #
    sseq1d
    eulerpart.t
    elrab2
    @15
    cfn
    wcel
    @9
    vf
    cA
    cR
    @16
    @15
    @5
    cfn
    @17
    eleq1d
    eulerpart.r
    elab4g
    anbi12i
    cA
    cT
    cR
    elin
    @3
    @9
    @6
    wa
    #
    wa
    @3
    @8
    wa
    #
    @18
    wa
    @12
    @11
    @3
    @19
    @18
    @3
    @8
    cA
    @2
    elex
    pm4.71i
    anbi1i
    @3
    @9
    @6
    3anass
    @3
    @6
    @8
    @9
    an42
    3bitr4i
    3bitr4i
end
