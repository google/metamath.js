include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "rspc2ev.mm"
include "mp3an3.mm"
include "2rexbidv.mm"
include "3expa.mm"
include "4sqlem2.mm"
include "sylibr.mm"
include "sylan2.mm"

theorem 4sqlem3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
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
  disjoint C n
  disjoint D n
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
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
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
  assert |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) ) -> ( ( ( A ^ 2 ) + ( B ^ 2 ) ) + ( ( C ^ 2 ) + ( D ^ 2 ) ) ) e. S )

  proof
    cC
    cz
    wcel
    #
    cD
    cz
    wcel
    #
    wa
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    #
    cC
    c2
    cexp
    co
    #
    cD
    c2
    cexp
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    @7
    vc
    cv
    #
    c2
    cexp
    co
    #
    vd
    cv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    wceq
    #
    vd
    cz
    wrex
    vc
    cz
    wrex
    #
    @11
    cS
    wcel
    #
    @0
    @1
    @11
    @11
    wceq
    #
    @19
    @11
    eqid
    @18
    @21
    @11
    @7
    @8
    @15
    caddc
    co
    #
    caddc
    co
    #
    wceq
    vc
    vd
    cC
    cD
    cz
    cz
    @12
    cC
    wceq
    #
    @17
    @23
    @11
    @24
    @16
    @22
    @7
    caddc
    @24
    @13
    @8
    @15
    caddc
    @12
    cC
    c2
    cexp
    oveq1
    oveq1d
    oveq2d
    eqeq2d
    @14
    cD
    wceq
    #
    @23
    @11
    @11
    @25
    @22
    @10
    @7
    caddc
    @25
    @15
    @9
    @8
    caddc
    @14
    cD
    c2
    cexp
    oveq1
    oveq2d
    oveq2d
    eqeq2d
    rspc2ev
    mp3an3
    @4
    @19
    wa
    @11
    va
    cv
    #
    c2
    cexp
    co
    #
    vb
    cv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    @16
    caddc
    co
    #
    wceq
    #
    vd
    cz
    wrex
    vc
    cz
    wrex
    #
    vb
    cz
    wrex
    va
    cz
    wrex
    #
    @20
    @2
    @3
    @19
    @34
    @33
    @19
    @11
    @5
    @29
    caddc
    co
    #
    @16
    caddc
    co
    #
    wceq
    #
    vd
    cz
    wrex
    vc
    cz
    wrex
    va
    vb
    cA
    cB
    cz
    cz
    @26
    cA
    wceq
    #
    @32
    @37
    vc
    vd
    cz
    cz
    @38
    @31
    @36
    @11
    @38
    @30
    @35
    @16
    caddc
    @38
    @27
    @5
    @29
    caddc
    @26
    cA
    c2
    cexp
    oveq1
    oveq1d
    oveq1d
    eqeq2d
    2rexbidv
    @28
    cB
    wceq
    #
    @37
    @18
    vc
    vd
    cz
    cz
    @39
    @36
    @17
    @11
    @39
    @35
    @7
    @16
    caddc
    @39
    @29
    @6
    @5
    caddc
    @28
    cB
    c2
    cexp
    oveq1
    oveq2d
    oveq1d
    eqeq2d
    2rexbidv
    rspc2ev
    3expa
    vx
    vy
    vz
    vw
    @11
    cS
    vn
    va
    vb
    vc
    vd
    4sq.1
    4sqlem2
    sylibr
    sylan2
end
