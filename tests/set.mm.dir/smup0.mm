include "cc0.mm"
include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "wceq.mm"
include "c0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cif.mm"
include "cmpt.mm"
include "cz.mm"
include "wcel.mm"
include "0z.mm"
include "cpw.mm"
include "wa.mm"
include "crab.mm"
include "csad.mm"
include "cmpt2.mm"
include "cseq.mm"
include "fveq1i.mm"
include "seq1.mm"
include "syl5eq.mm"
include "mp1i.mm"
include "0nn0.mm"
include "iftrue.mm"
include "eqid.mm"
include "0ex.mm"
include "fvmpt.mm"
include "eqtrd.mm"

theorem smup0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  let cM: class M
  assume smuval.a: |- ( ph -> A C_ NN0 )
  assume smuval.b: |- ( ph -> B C_ NN0 )
  assume smuval.p: |- P = seq 0 ( ( p e. ~P NN0 , m e. NN0 |-> ( p sadd { n e. NN0 | ( m e. A /\ ( n - m ) e. B ) } ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )

  disjoint m n
  disjoint m p
  disjoint A m
  disjoint n p
  disjoint A n
  disjoint A p
  disjoint n ph
  disjoint B m
  disjoint B n
  disjoint B p
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint p x
  disjoint p y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint N k
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint M k
  disjoint M x
  disjoint P k
  disjoint P x
  disjoint P y
  assert |- ( ph -> ( P ` 0 ) = (/) )

  proof
    wph
    cc0
    cP
    cfv
    #
    cc0
    vn
    cn0
    vn
    cv
    #
    cc0
    wceq
    #
    c0
    @1
    c1
    cmin
    co
    #
    cif
    #
    cmpt
    #
    cfv
    #
    c0
    cc0
    cz
    wcel
    #
    @0
    @6
    wceq
    wph
    0z
    @7
    @0
    cc0
    vp
    vm
    cn0
    cpw
    cn0
    vp
    cv
    vm
    cv
    #
    cA
    wcel
    @1
    @8
    cmin
    co
    cB
    wcel
    wa
    vn
    cn0
    crab
    csad
    co
    cmpt2
    #
    @5
    cc0
    cseq
    #
    cfv
    @6
    cc0
    cP
    @10
    smuval.p
    fveq1i
    @9
    @5
    cc0
    seq1
    syl5eq
    mp1i
    cc0
    cn0
    wcel
    @6
    c0
    wceq
    wph
    0nn0
    vn
    cc0
    @4
    c0
    cn0
    @5
    @2
    c0
    @3
    iftrue
    @5
    eqid
    0ex
    fvmpt
    mp1i
    eqtrd
end
