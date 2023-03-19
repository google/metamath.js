include "cgz.mm"
include "wcel.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "cre.mm"
include "cim.mm"
include "gzcn.mm"
include "absvalsq2d.mm"
include "oveqan12d.mm"
include "cz.mm"
include "cc.mm"
include "elgz.mm"
include "simp2bi.mm"
include "simp3bi.mm"
include "jca.mm"
include "4sqlem3.mm"
include "syl2an.mm"
include "eqeltrd.mm"

theorem 4sqlem4a
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cS: class S
  let vn: setvar n
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cE: class E
  let cG: class G
  let cH: class H
  let vj: setvar j
  let vk: setvar k
  let vv: setvar v
  let cC: class C
  let cD: class D
  let cF: class F
  let vi: setvar i
  let vu: setvar u
  let cM: class M
  let vm: setvar m
  let cN: class N
  let cP: class P
  let wph: wff ph
  let cT: class T
  let cR: class R
  assume 4sq.1: |- S = { n | E. x e. ZZ E. y e. ZZ E. z e. ZZ E. w e. ZZ n = ( ( ( x ^ 2 ) + ( y ^ 2 ) ) + ( ( z ^ 2 ) + ( w ^ 2 ) ) ) }

  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B n
  disjoint A n
  disjoint S n
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a n
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b c
  disjoint b d
  disjoint b n
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint c d
  disjoint c n
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint d n
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint E n
  disjoint G n
  disjoint H n
  disjoint a j
  disjoint a k
  disjoint a v
  disjoint A a
  disjoint b j
  disjoint b k
  disjoint b v
  disjoint A b
  disjoint c j
  disjoint c k
  disjoint c v
  disjoint A c
  disjoint d j
  disjoint d k
  disjoint d v
  disjoint A d
  disjoint j k
  disjoint j n
  disjoint j v
  disjoint A j
  disjoint k n
  disjoint k v
  disjoint A k
  disjoint n v
  disjoint A v
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C n
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D n
  disjoint F j
  disjoint F n
  disjoint a i
  disjoint a u
  disjoint M a
  disjoint b i
  disjoint b u
  disjoint M b
  disjoint c i
  disjoint c u
  disjoint M c
  disjoint d i
  disjoint d u
  disjoint M d
  disjoint i k
  disjoint i n
  disjoint i u
  disjoint M i
  disjoint k u
  disjoint M k
  disjoint n u
  disjoint M n
  disjoint M u
  disjoint k m
  disjoint N k
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint N m
  disjoint N n
  disjoint u v
  disjoint N u
  disjoint N v
  disjoint a m
  disjoint P a
  disjoint b m
  disjoint P b
  disjoint c m
  disjoint P c
  disjoint d m
  disjoint P d
  disjoint i j
  disjoint i m
  disjoint i v
  disjoint P i
  disjoint j m
  disjoint j u
  disjoint P j
  disjoint P k
  disjoint P m
  disjoint P n
  disjoint P u
  disjoint P v
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph u
  disjoint ph v
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S i
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S u
  disjoint S v
  disjoint T k
  disjoint T u
  disjoint R i
  assert |- ( ( A e. Z[i] /\ B e. Z[i] ) -> ( ( ( abs ` A ) ^ 2 ) + ( ( abs ` B ) ^ 2 ) ) e. S )

  proof
    cA
    cgz
    wcel
    #
    cB
    cgz
    wcel
    #
    wa
    cA
    cabs
    cfv
    c2
    cexp
    co
    #
    cB
    cabs
    cfv
    c2
    cexp
    co
    #
    caddc
    co
    cA
    cre
    cfv
    #
    c2
    cexp
    co
    cA
    cim
    cfv
    #
    c2
    cexp
    co
    caddc
    co
    #
    cB
    cre
    cfv
    #
    c2
    cexp
    co
    cB
    cim
    cfv
    #
    c2
    cexp
    co
    caddc
    co
    #
    caddc
    co
    #
    cS
    @0
    @1
    @2
    @6
    @3
    @9
    caddc
    @0
    cA
    cA
    gzcn
    absvalsq2d
    @1
    cB
    cB
    gzcn
    absvalsq2d
    oveqan12d
    @0
    @4
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    wa
    @7
    cz
    wcel
    #
    @8
    cz
    wcel
    #
    wa
    @10
    cS
    wcel
    @1
    @0
    @11
    @12
    @0
    cA
    cc
    wcel
    #
    @11
    @12
    cA
    elgz
    #
    simp2bi
    @0
    @15
    @11
    @12
    @16
    simp3bi
    jca
    @1
    @13
    @14
    @1
    cB
    cc
    wcel
    #
    @13
    @14
    cB
    elgz
    #
    simp2bi
    @1
    @17
    @13
    @14
    @18
    simp3bi
    jca
    vx
    vy
    vz
    vw
    @4
    @5
    @7
    @8
    cS
    vn
    4sq.1
    4sqlem3
    syl2an
    eqeltrd
end
