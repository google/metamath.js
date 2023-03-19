include "cn.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cuz.mm"
include "eqid.mm"
include "cz.mm"
include "nnz.mm"
include "adantl.mm"
include "eqidd.mm"
include "cr.mm"
include "wf.mm"
include "rpnnen2lem2.mm"
include "ad2antrr.mm"
include "eluznn.mm"
include "adantll.mm"
include "ffvelrnd.mm"
include "rpnnen2lem5.mm"
include "isumrecl.mm"

theorem rpnnen2lem6
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cM: class M
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let wph: wff ph
  let cN: class N
  assume rpnnen2.1: |- F = ( x e. ~P NN |-> ( n e. NN |-> if ( n e. x , ( ( 1 / 3 ) ^ n ) , 0 ) ) )

  disjoint n x
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint A n
  disjoint A x
  disjoint F k
  disjoint M k
  disjoint M n
  disjoint M x
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B k
  disjoint B n
  disjoint B x
  disjoint k m
  disjoint k y
  disjoint k z
  disjoint F m
  disjoint F y
  disjoint F z
  disjoint k ph
  disjoint N n
  assert |- ( ( A C_ NN /\ M e. NN ) -> sum_ k e. ( ZZ>= ` M ) ( ( F ` A ) ` k ) e. RR )

  proof
    cA
    cn
    wss
    #
    cM
    cn
    wcel
    #
    wa
    #
    vk
    cv
    #
    cA
    cF
    cfv
    #
    cfv
    #
    vk
    @4
    cM
    cM
    cuz
    cfv
    #
    @6
    eqid
    @1
    cM
    cz
    wcel
    @0
    cM
    nnz
    adantl
    @2
    @3
    @6
    wcel
    #
    wa
    #
    @5
    eqidd
    @8
    cn
    cr
    @3
    @4
    @0
    cn
    cr
    @4
    wf
    @1
    @7
    vx
    cA
    vn
    cF
    rpnnen2.1
    rpnnen2lem2
    ad2antrr
    @1
    @7
    @3
    cn
    wcel
    @0
    @3
    cM
    eluznn
    adantll
    ffvelrnd
    vx
    cA
    vn
    cF
    cM
    rpnnen2.1
    rpnnen2lem5
    isumrecl
end
