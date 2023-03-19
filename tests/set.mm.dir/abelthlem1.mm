include "c1.mm"
include "cabs.mm"
include "cfv.mm"
include "caddc.mm"
include "cv.mm"
include "cc.mm"
include "cn0.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cmpt.mm"
include "cc0.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "crab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "abs1.mm"
include "eqid.mm"
include "1cnd.mm"
include "feqmptd.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "mulid1d.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "oveq1.mm"
include "cz.mm"
include "nn0z.mm"
include "1exp.mm"
include "syl.mm"
include "sylan9eq.mm"
include "oveq2d.mm"
include "nn0ex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "syl6eqr.mm"
include "seqeq3d.mm"
include "eqeltrrd.mm"
include "radcnvle.mm"
include "syl5eqbrr.mm"

theorem abelthlem1
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let vn: setvar n
  let vr: setvar r
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  let cR: class R
  let cX: class X
  let vt: setvar t
  let vv: setvar v
  let cN: class N
  let cF: class F
  let cS: class S
  assume abelth.1: |- ( ph -> A : NN0 --> CC )
  assume abelth.2: |- ( ph -> seq 0 ( + , A ) e. dom ~~> )

  disjoint n z
  disjoint n r
  disjoint r z
  disjoint A n
  disjoint A r
  disjoint A z
  disjoint n ph
  disjoint ph r
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint M i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint M j
  disjoint k m
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint M k
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint M m
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint M n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint M w
  disjoint x y
  disjoint x z
  disjoint M x
  disjoint y z
  disjoint M y
  disjoint M z
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R m
  disjoint R n
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint i r
  disjoint X i
  disjoint j r
  disjoint X j
  disjoint k r
  disjoint X k
  disjoint X n
  disjoint r x
  disjoint X r
  disjoint X x
  disjoint X z
  disjoint i t
  disjoint i v
  disjoint A i
  disjoint j t
  disjoint j v
  disjoint A j
  disjoint k t
  disjoint k v
  disjoint A k
  disjoint m r
  disjoint m t
  disjoint m v
  disjoint A m
  disjoint n t
  disjoint n v
  disjoint r t
  disjoint r v
  disjoint r w
  disjoint r y
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint N k
  disjoint N n
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint F i
  disjoint F j
  disjoint F r
  disjoint F w
  disjoint F y
  disjoint S i
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S r
  disjoint S w
  disjoint S x
  disjoint S y
  assert |- ( ph -> 1 <_ sup ( { r e. RR | seq 0 ( + , ( ( z e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( z ^ n ) ) ) ) ` r ) ) e. dom ~~> } , RR* , < ) )

  proof
    wph
    c1
    c1
    cabs
    cfv
    caddc
    vr
    cv
    vz
    cc
    vn
    cn0
    vn
    cv
    #
    cA
    cfv
    #
    vz
    cv
    #
    @0
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cmpt
    #
    cfv
    cc0
    cseq
    cli
    cdm
    #
    wcel
    vr
    cr
    crab
    cxr
    clt
    csup
    #
    cle
    abs1
    wph
    vz
    cA
    @8
    vn
    @6
    c1
    vr
    @6
    eqid
    #
    abelth.1
    @8
    eqid
    wph
    1cnd
    wph
    caddc
    cA
    cc0
    cseq
    caddc
    c1
    @6
    cfv
    #
    cc0
    cseq
    @7
    wph
    cA
    @10
    caddc
    cc0
    wph
    cA
    vn
    cn0
    @1
    c1
    cmul
    co
    #
    cmpt
    #
    @10
    wph
    cA
    vn
    cn0
    @1
    cmpt
    @12
    wph
    vn
    cn0
    cc
    cA
    abelth.1
    feqmptd
    wph
    vn
    cn0
    @11
    @1
    wph
    @0
    cn0
    wcel
    #
    wa
    @1
    wph
    cn0
    cc
    @0
    cA
    abelth.1
    ffvelrnda
    mulid1d
    mpteq2dva
    eqtr4d
    c1
    cc
    wcel
    @10
    @12
    wceq
    ax-1cn
    vz
    c1
    @5
    @12
    cc
    @6
    @2
    c1
    wceq
    #
    vn
    cn0
    @4
    @11
    @14
    @13
    wa
    @3
    c1
    @1
    cmul
    @14
    @13
    @3
    c1
    @0
    cexp
    co
    #
    c1
    @2
    c1
    @0
    cexp
    oveq1
    @13
    @0
    cz
    wcel
    @15
    c1
    wceq
    @0
    nn0z
    @0
    1exp
    syl
    sylan9eq
    oveq2d
    mpteq2dva
    @9
    vn
    cn0
    @11
    nn0ex
    mptex
    fvmpt
    ax-mp
    syl6eqr
    seqeq3d
    abelth.2
    eqeltrrd
    radcnvle
    syl5eqbrr
end
