include "wcel.mm"
include "cc.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "csn.mm"
include "eldifad.mm"
include "cv.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "elrab2.mm"
include "sylib.mm"

theorem abelthlem7a
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cX: class X
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vw: setvar w
  let vy: setvar y
  let cR: class R
  let vr: setvar r
  let vt: setvar t
  let vv: setvar v
  let cN: class N
  assume abelth.1: |- ( ph -> A : NN0 --> CC )
  assume abelth.2: |- ( ph -> seq 0 ( + , A ) e. dom ~~> )
  assume abelth.3: |- ( ph -> M e. RR )
  assume abelth.4: |- ( ph -> 0 <_ M )
  assume abelth.5: |- S = { z e. CC | ( abs ` ( 1 - z ) ) <_ ( M x. ( 1 - ( abs ` z ) ) ) }
  assume abelth.6: |- F = ( x e. S |-> sum_ n e. NN0 ( ( A ` n ) x. ( x ^ n ) ) )
  assume abelth.7: |- ( ph -> seq 0 ( + , A ) ~~> 0 )
  assume abelthlem6.1: |- ( ph -> X e. ( S \ { 1 } ) )

  disjoint n x
  disjoint n z
  disjoint M n
  disjoint x z
  disjoint M x
  disjoint M z
  disjoint X n
  disjoint X x
  disjoint X z
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
  disjoint r x
  disjoint r z
  disjoint X r
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
  assert |- ( ph -> ( X e. CC /\ ( abs ` ( 1 - X ) ) <_ ( M x. ( 1 - ( abs ` X ) ) ) ) )

  proof
    wph
    cX
    cS
    wcel
    cX
    cc
    wcel
    c1
    cX
    cmin
    co
    #
    cabs
    cfv
    #
    cM
    c1
    cX
    cabs
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    wa
    wph
    cX
    cS
    c1
    csn
    abelthlem6.1
    eldifad
    c1
    vz
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cM
    c1
    @6
    cabs
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    cle
    wbr
    @5
    vz
    cX
    cc
    cS
    @6
    cX
    wceq
    #
    @8
    @1
    @11
    @4
    cle
    @12
    @7
    @0
    cabs
    @6
    cX
    c1
    cmin
    oveq2
    fveq2d
    @12
    @10
    @3
    cM
    cmul
    @12
    @9
    @2
    c1
    cmin
    @6
    cX
    cabs
    fveq2
    oveq2d
    oveq2d
    breq12d
    abelth.5
    elrab2
    sylib
end
