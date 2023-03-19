include "wss.mm"
include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cuz.mm"
include "eqid.mm"
include "simp3.mm"
include "nnzd.mm"
include "wa.mm"
include "eqidd.mm"
include "cr.mm"
include "eluznn.mm"
include "sylan.mm"
include "wf.mm"
include "sstr.mm"
include "3adant3.mm"
include "rpnnen2lem2.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "3ad2ant2.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "rpnnen2lem4.mm"
include "simprd.mm"
include "3expa.mm"
include "3adantl3.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "rpnnen2lem5.mm"
include "stoic3.mm"
include "3adant1.mm"
include "isumle.mm"

theorem rpnnen2lem7
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cM: class M
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph
  let cN: class N
  assume rpnnen2.1: |- F = ( x e. ~P NN |-> ( n e. NN |-> if ( n e. x , ( ( 1 / 3 ) ^ n ) , 0 ) ) )

  disjoint n x
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint A n
  disjoint A x
  disjoint B k
  disjoint B n
  disjoint B x
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
  disjoint k m
  disjoint k y
  disjoint k z
  disjoint F m
  disjoint F y
  disjoint F z
  disjoint k ph
  disjoint N n
  assert |- ( ( A C_ B /\ B C_ NN /\ M e. NN ) -> sum_ k e. ( ZZ>= ` M ) ( ( F ` A ) ` k ) <_ sum_ k e. ( ZZ>= ` M ) ( ( F ` B ) ` k ) )

  proof
    cA
    cB
    wss
    #
    cB
    cn
    wss
    #
    cM
    cn
    wcel
    #
    w3a
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
    @4
    cB
    cF
    cfv
    #
    cfv
    #
    vk
    @5
    @7
    cM
    cM
    cuz
    cfv
    #
    @9
    eqid
    @3
    cM
    @0
    @1
    @2
    simp3
    #
    nnzd
    @3
    @4
    @9
    wcel
    #
    wa
    #
    @6
    eqidd
    @3
    @11
    @4
    cn
    wcel
    #
    @6
    cr
    wcel
    @3
    @2
    @11
    @13
    @10
    @4
    cM
    eluznn
    sylan
    #
    @3
    cn
    cr
    @4
    @5
    @3
    cA
    cn
    wss
    #
    cn
    cr
    @5
    wf
    @0
    @1
    @15
    @2
    cA
    cB
    cn
    sstr
    #
    3adant3
    vx
    cA
    vn
    cF
    rpnnen2.1
    rpnnen2lem2
    syl
    ffvelrnda
    syldan
    @12
    @8
    eqidd
    @3
    @11
    @13
    @8
    cr
    wcel
    @14
    @3
    cn
    cr
    @4
    @7
    @1
    @0
    cn
    cr
    @7
    wf
    @2
    vx
    cB
    vn
    cF
    rpnnen2.1
    rpnnen2lem2
    3ad2ant2
    ffvelrnda
    syldan
    @3
    @11
    @13
    @6
    @8
    cle
    wbr
    #
    @14
    @0
    @1
    @13
    @17
    @2
    @0
    @1
    @13
    @17
    @0
    @1
    @13
    w3a
    cc0
    @6
    cle
    wbr
    @17
    vx
    cA
    cB
    vk
    vn
    cF
    rpnnen2.1
    rpnnen2lem4
    simprd
    3expa
    3adantl3
    syldan
    @0
    @1
    @15
    @2
    caddc
    @5
    cM
    cseq
    cli
    cdm
    #
    wcel
    @16
    vx
    cA
    vn
    cF
    cM
    rpnnen2.1
    rpnnen2lem5
    stoic3
    @1
    @2
    caddc
    @7
    cM
    cseq
    @18
    wcel
    @0
    vx
    cB
    vn
    cF
    cM
    rpnnen2.1
    rpnnen2lem5
    3adant1
    isumle
end
