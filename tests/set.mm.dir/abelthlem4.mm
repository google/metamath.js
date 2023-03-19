include "cn0.mm"
include "cv.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "csu.mm"
include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmpt.mm"
include "cc0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "wf.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "wss.mm"
include "c1.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "a1i.mm"
include "sselda.mm"
include "expcl.mm"
include "sylan.mm"
include "mulcld.mm"
include "abelthlem3.mm"
include "isumcl.mm"
include "fmptd.mm"

theorem abelthlem4
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cM: class M
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vw: setvar w
  let vy: setvar y
  let cR: class R
  let vr: setvar r
  let cX: class X
  let vt: setvar t
  let vv: setvar v
  let cN: class N
  assume abelth.1: |- ( ph -> A : NN0 --> CC )
  assume abelth.2: |- ( ph -> seq 0 ( + , A ) e. dom ~~> )
  assume abelth.3: |- ( ph -> M e. RR )
  assume abelth.4: |- ( ph -> 0 <_ M )
  assume abelth.5: |- S = { z e. CC | ( abs ` ( 1 - z ) ) <_ ( M x. ( 1 - ( abs ` z ) ) ) }
  assume abelth.6: |- F = ( x e. S |-> sum_ n e. NN0 ( ( A ` n ) x. ( x ^ n ) ) )

  disjoint n x
  disjoint n z
  disjoint M n
  disjoint x z
  disjoint M x
  disjoint M z
  disjoint A n
  disjoint A x
  disjoint A z
  disjoint n ph
  disjoint ph x
  disjoint S n
  disjoint S x
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
  disjoint n y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint M w
  disjoint x y
  disjoint y z
  disjoint M y
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
  disjoint n r
  disjoint X n
  disjoint r x
  disjoint r z
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
  disjoint A r
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
  disjoint A y
  disjoint N k
  disjoint N n
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph r
  disjoint ph v
  disjoint ph w
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
  disjoint S r
  disjoint S w
  disjoint S y
  assert |- ( ph -> F : S --> CC )

  proof
    wph
    vx
    cS
    cn0
    vn
    cv
    #
    cA
    cfv
    #
    vx
    cv
    #
    @0
    cexp
    co
    #
    cmul
    co
    #
    vn
    csu
    cc
    cF
    wph
    @2
    cS
    wcel
    #
    wa
    #
    @4
    vn
    vm
    cn0
    vm
    cv
    #
    cA
    cfv
    #
    @2
    @7
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cc0
    cn0
    nn0uz
    @6
    0zd
    @0
    cn0
    wcel
    #
    @0
    @11
    cfv
    @4
    wceq
    @6
    vm
    @0
    @10
    @4
    cn0
    @11
    @7
    @0
    wceq
    @8
    @1
    @9
    @3
    cmul
    @7
    @0
    cA
    fveq2
    @7
    @0
    @2
    cexp
    oveq2
    oveq12d
    @11
    eqid
    @1
    @3
    cmul
    ovex
    fvmpt
    adantl
    @6
    @12
    wa
    @1
    @3
    @6
    cn0
    cc
    @0
    cA
    wph
    cn0
    cc
    cA
    wf
    @5
    abelth.1
    adantr
    ffvelrnda
    @6
    @2
    cc
    wcel
    @12
    @3
    cc
    wcel
    wph
    cS
    cc
    @2
    cS
    cc
    wss
    wph
    cS
    c1
    vz
    cv
    #
    cmin
    co
    cabs
    cfv
    cM
    c1
    @13
    cabs
    cfv
    cmin
    co
    cmul
    co
    cle
    wbr
    #
    vz
    cc
    crab
    cc
    abelth.5
    @14
    vz
    cc
    ssrab2
    eqsstri
    a1i
    sselda
    @2
    @0
    expcl
    sylan
    mulcld
    wph
    vz
    cA
    cS
    vm
    cM
    @2
    abelth.1
    abelth.2
    abelth.3
    abelth.4
    abelth.5
    abelthlem3
    isumcl
    abelth.6
    fmptd
end
