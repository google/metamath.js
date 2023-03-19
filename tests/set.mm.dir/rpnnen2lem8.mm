include "cn.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "cuz.mm"
include "nnuz.mm"
include "eqid.mm"
include "simpr.mm"
include "eqidd.mm"
include "cr.mm"
include "wf.mm"
include "rpnnen2lem2.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "1nn.mm"
include "rpnnen2lem5.mm"
include "mpan2.mm"
include "isumsplit.mm"

theorem rpnnen2lem8
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
  assert |- ( ( A C_ NN /\ M e. NN ) -> sum_ k e. NN ( ( F ` A ) ` k ) = ( sum_ k e. ( 1 ... ( M - 1 ) ) ( ( F ` A ) ` k ) + sum_ k e. ( ZZ>= ` M ) ( ( F ` A ) ` k ) ) )

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
    c1
    cM
    cM
    cuz
    cfv
    #
    cn
    nnuz
    @6
    eqid
    @0
    @1
    simpr
    @2
    @3
    cn
    wcel
    wa
    #
    @5
    eqidd
    @7
    @5
    @2
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
    vx
    cA
    vn
    cF
    rpnnen2.1
    rpnnen2lem2
    adantr
    ffvelrnda
    recnd
    @0
    caddc
    @4
    c1
    cseq
    cli
    cdm
    wcel
    #
    @1
    @0
    c1
    cn
    wcel
    @8
    1nn
    vx
    cA
    vn
    cF
    c1
    rpnnen2.1
    rpnnen2lem5
    mpan2
    adantr
    isumsplit
end
