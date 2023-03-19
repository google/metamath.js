include "cz.mm"
include "cn0.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "id.mm"
include "oveq2.mm"
include "oveqan12d.mm"
include "oveq1.mm"
include "opeq12d.mm"
include "opex.mm"
include "ovmpt2a.mm"

theorem dyadval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let va: setvar a
  let vb: setvar b
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vw: setvar w
  let vz: setvar z
  let wph: wff ph
  let vi: setvar i
  let vr: setvar r
  let cD: class D
  let cG: class G
  assume dyadmbl.1: |- F = ( x e. ZZ , y e. NN0 |-> <. ( x / ( 2 ^ y ) ) , ( ( x + 1 ) / ( 2 ^ y ) ) >. )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint c d
  disjoint c f
  disjoint c x
  disjoint c y
  disjoint d f
  disjoint d x
  disjoint d y
  disjoint f x
  disjoint f y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint C x
  disjoint C y
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint a t
  disjoint a w
  disjoint a z
  disjoint a ph
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b t
  disjoint b w
  disjoint b z
  disjoint b ph
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f w
  disjoint f z
  disjoint f ph
  disjoint m n
  disjoint m t
  disjoint m w
  disjoint m z
  disjoint m ph
  disjoint n t
  disjoint n w
  disjoint n z
  disjoint n ph
  disjoint t w
  disjoint t z
  disjoint ph t
  disjoint w z
  disjoint ph w
  disjoint ph z
  disjoint a i
  disjoint a r
  disjoint A a
  disjoint b i
  disjoint b r
  disjoint A b
  disjoint c i
  disjoint c m
  disjoint c n
  disjoint c r
  disjoint c t
  disjoint c w
  disjoint c z
  disjoint A c
  disjoint d i
  disjoint d m
  disjoint d n
  disjoint d r
  disjoint d t
  disjoint d w
  disjoint d z
  disjoint A d
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint i t
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint A i
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint D x
  disjoint D y
  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G m
  disjoint G n
  disjoint G t
  disjoint G z
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F m
  disjoint F n
  disjoint F r
  disjoint F w
  disjoint F z
  assert |- ( ( A e. ZZ /\ B e. NN0 ) -> ( A F B ) = <. ( A / ( 2 ^ B ) ) , ( ( A + 1 ) / ( 2 ^ B ) ) >. )

  proof
    vx
    vy
    cA
    cB
    cz
    cn0
    vx
    cv
    #
    c2
    vy
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    @0
    c1
    caddc
    co
    #
    @2
    cdiv
    co
    #
    cop
    cA
    c2
    cB
    cexp
    co
    #
    cdiv
    co
    #
    cA
    c1
    caddc
    co
    #
    @6
    cdiv
    co
    #
    cop
    cF
    @0
    cA
    wceq
    #
    @1
    cB
    wceq
    #
    wa
    @3
    @7
    @5
    @9
    @10
    @11
    @0
    cA
    @2
    @6
    cdiv
    @10
    id
    @1
    cB
    c2
    cexp
    oveq2
    #
    oveqan12d
    @10
    @11
    @4
    @8
    @2
    @6
    cdiv
    @0
    cA
    c1
    caddc
    oveq1
    @12
    oveqan12d
    opeq12d
    dyadmbl.1
    @7
    @9
    opex
    ovmpt2a
end
