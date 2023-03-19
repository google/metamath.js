include "cbits.mm"
include "cv.mm"
include "cres.mm"
include "ccom.mm"
include "cfv.mm"
include "cima.mm"
include "cn.mm"
include "cind.mm"
include "cin.mm"
include "wceq.mm"
include "reseq1.mm"
include "coeq2d.mm"
include "fveq2d.mm"
include "imaeq2d.mm"
include "fvex.mm"
include "fvmpt.mm"

theorem eulerpartlemgv
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
  let vo: setvar o
  let cF: class F
  let cG: class G
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
  assume eulerpart.g: |- G = ( o e. ( T i^i R ) |-> ( ( _Ind ` NN ) ` ( F " ( M ` ( bits o. ( o |` J ) ) ) ) ) )

  disjoint A o
  disjoint F o
  disjoint J o
  disjoint M o
  disjoint R o
  disjoint T o
  assert |- ( A e. ( T i^i R ) -> ( G ` A ) = ( ( _Ind ` NN ) ` ( F " ( M ` ( bits o. ( A |` J ) ) ) ) ) )

  proof
    vo
    cA
    cF
    cbits
    vo
    cv
    #
    cJ
    cres
    #
    ccom
    #
    cM
    cfv
    #
    cima
    #
    cn
    cind
    cfv
    #
    cfv
    cF
    cbits
    cA
    cJ
    cres
    #
    ccom
    #
    cM
    cfv
    #
    cima
    #
    @5
    cfv
    cT
    cR
    cin
    cG
    @0
    cA
    wceq
    #
    @4
    @9
    @5
    @10
    @3
    @8
    cF
    @10
    @2
    @7
    cM
    @10
    @1
    @6
    cbits
    @0
    cA
    cJ
    reseq1
    coeq2d
    fveq2d
    imaeq2d
    fveq2d
    eulerpart.g
    @9
    @5
    fvex
    fvmpt
end
