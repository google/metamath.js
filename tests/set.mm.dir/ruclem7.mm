include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cc0.mm"
include "cseq.mm"
include "cuz.mm"
include "wceq.mm"
include "simpr.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "seqp1.mm"
include "syl.mm"
include "fveq1i.mm"
include "oveq1i.mm"
include "3eqtr4g.mm"
include "wne.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "adantl.mm"
include "nnne0d.mm"
include "necomd.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "equncomi.mm"
include "fvunsn.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem ruclem7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cN: class N
  let vw: setvar w
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vn: setvar n
  let vk: setvar k
  let cM: class M
  let cS: class S
  assume ruc.1: |- ( ph -> F : NN --> RR )
  assume ruc.2: |- ( ph -> D = ( x e. ( RR X. RR ) , y e. RR |-> [_ ( ( ( 1st ` x ) + ( 2nd ` x ) ) / 2 ) / m ]_ if ( m < y , <. ( 1st ` x ) , m >. , <. ( ( m + ( 2nd ` x ) ) / 2 ) , ( 2nd ` x ) >. ) ) )
  assume ruc.4: |- C = ( { <. 0 , <. 0 , 1 >. >. } u. F )
  assume ruc.5: |- G = seq 0 ( D , C )

  disjoint m x
  disjoint m y
  disjoint x y
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint G m
  disjoint G x
  disjoint G y
  disjoint N m
  disjoint N x
  disjoint N y
  disjoint m w
  disjoint w x
  disjoint w y
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint w z
  disjoint C w
  disjoint C z
  disjoint m n
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint G k
  disjoint G n
  disjoint G z
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint N k
  disjoint k w
  disjoint k ph
  disjoint n w
  disjoint n ph
  disjoint ph w
  disjoint ph z
  disjoint D w
  disjoint D z
  disjoint S n
  disjoint S z
  assert |- ( ( ph /\ N e. NN0 ) -> ( G ` ( N + 1 ) ) = ( ( G ` N ) D ( F ` ( N + 1 ) ) ) )

  proof
    wph
    cN
    cn0
    wcel
    #
    wa
    #
    cN
    c1
    caddc
    co
    #
    cG
    cfv
    #
    cN
    cG
    cfv
    #
    @2
    cC
    cfv
    #
    cD
    co
    #
    @4
    @2
    cF
    cfv
    #
    cD
    co
    @1
    @2
    cD
    cC
    cc0
    cseq
    #
    cfv
    #
    cN
    @8
    cfv
    #
    @5
    cD
    co
    #
    @3
    @6
    @1
    cN
    cc0
    cuz
    cfv
    #
    wcel
    @9
    @11
    wceq
    @1
    cN
    cn0
    @12
    wph
    @0
    simpr
    nn0uz
    syl6eleq
    cD
    cC
    cc0
    cN
    seqp1
    syl
    @2
    cG
    @8
    ruc.5
    fveq1i
    @4
    @10
    @5
    cD
    cN
    cG
    @8
    ruc.5
    fveq1i
    oveq1i
    3eqtr4g
    @1
    @5
    @7
    @4
    cD
    @1
    cc0
    @2
    wne
    #
    @5
    @7
    wceq
    @1
    @2
    cc0
    @1
    @2
    @0
    @2
    cn
    wcel
    wph
    cN
    nn0p1nn
    adantl
    nnne0d
    necomd
    @13
    @5
    @2
    cF
    cc0
    cc0
    c1
    cop
    #
    cop
    csn
    #
    cun
    #
    cfv
    @7
    @2
    cC
    @16
    cC
    @15
    cF
    ruc.4
    equncomi
    fveq1i
    cF
    cc0
    @14
    @2
    fvunsn
    syl5eq
    syl
    oveq2d
    eqtrd
end
