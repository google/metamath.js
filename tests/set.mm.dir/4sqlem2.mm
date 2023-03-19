include "wcel.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "cab.mm"
include "eleq2i.mm"
include "cvv.mm"
include "wa.mm"
include "wi.mm"
include "id.mm"
include "ovex.mm"
include "syl6eqel.mm"
include "a1i.mm"
include "rexlimdvva.mm"
include "rexlimivv.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "2rexbidv.mm"
include "oveq2d.mm"
include "cbvrex2v.mm"
include "eqeq1.mm"
include "syl5bb.mm"
include "elab3.mm"
include "bitri.mm"

theorem 4sqlem2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cS: class S
  let vn: setvar n
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cB: class B
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
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint A n
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S n
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B n
  disjoint E n
  disjoint G n
  disjoint H n
  disjoint a j
  disjoint a k
  disjoint a v
  disjoint b j
  disjoint b k
  disjoint b v
  disjoint c j
  disjoint c k
  disjoint c v
  disjoint d j
  disjoint d k
  disjoint d v
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
  disjoint S i
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S u
  disjoint S v
  disjoint T k
  disjoint T u
  disjoint R i
  assert |- ( A e. S <-> E. a e. ZZ E. b e. ZZ E. c e. ZZ E. d e. ZZ A = ( ( ( a ^ 2 ) + ( b ^ 2 ) ) + ( ( c ^ 2 ) + ( d ^ 2 ) ) ) )

  proof
    cA
    cS
    wcel
    cA
    vn
    cv
    #
    vx
    cv
    #
    c2
    cexp
    co
    #
    vy
    cv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    vz
    cv
    #
    c2
    cexp
    co
    #
    vw
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
    vw
    cz
    wrex
    vz
    cz
    wrex
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    #
    vn
    cab
    #
    wcel
    cA
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
    vb
    cz
    wrex
    va
    cz
    wrex
    #
    cS
    @15
    cA
    4sq.1
    eleq2i
    @14
    @29
    vn
    cA
    @28
    cA
    cvv
    wcel
    #
    va
    vb
    cz
    cz
    @16
    cz
    wcel
    @18
    cz
    wcel
    wa
    #
    @27
    @30
    vc
    vd
    cz
    cz
    @27
    @30
    wi
    @31
    @21
    cz
    wcel
    @23
    cz
    wcel
    wa
    wa
    @27
    cA
    @26
    cvv
    @27
    id
    @20
    @25
    caddc
    ovex
    syl6eqel
    a1i
    rexlimdvva
    rexlimivv
    @14
    @0
    @20
    @10
    caddc
    co
    #
    wceq
    #
    vw
    cz
    wrex
    vz
    cz
    wrex
    #
    vb
    cz
    wrex
    va
    cz
    wrex
    @0
    cA
    wceq
    #
    @29
    @13
    @34
    @0
    @17
    @4
    caddc
    co
    #
    @10
    caddc
    co
    #
    wceq
    #
    vw
    cz
    wrex
    vz
    cz
    wrex
    vx
    vy
    va
    vb
    cz
    cz
    vx
    va
    weq
    #
    @12
    @38
    vz
    vw
    cz
    cz
    @39
    @11
    @37
    @0
    @39
    @5
    @36
    @10
    caddc
    @39
    @2
    @17
    @4
    caddc
    @1
    @16
    c2
    cexp
    oveq1
    oveq1d
    oveq1d
    eqeq2d
    2rexbidv
    vy
    vb
    weq
    #
    @38
    @33
    vz
    vw
    cz
    cz
    @40
    @37
    @32
    @0
    @40
    @36
    @20
    @10
    caddc
    @40
    @4
    @19
    @17
    caddc
    @3
    @18
    c2
    cexp
    oveq1
    oveq2d
    oveq1d
    eqeq2d
    2rexbidv
    cbvrex2v
    @35
    @34
    @28
    va
    vb
    cz
    cz
    @34
    @0
    @26
    wceq
    #
    vd
    cz
    wrex
    vc
    cz
    wrex
    @35
    @28
    @33
    @41
    @0
    @20
    @22
    @9
    caddc
    co
    #
    caddc
    co
    #
    wceq
    vz
    vw
    vc
    vd
    cz
    cz
    vz
    vc
    weq
    #
    @32
    @43
    @0
    @44
    @10
    @42
    @20
    caddc
    @44
    @7
    @22
    @9
    caddc
    @6
    @21
    c2
    cexp
    oveq1
    oveq1d
    oveq2d
    eqeq2d
    vw
    vd
    weq
    #
    @43
    @26
    @0
    @45
    @42
    @25
    @20
    caddc
    @45
    @9
    @24
    @22
    caddc
    @8
    @23
    c2
    cexp
    oveq1
    oveq2d
    oveq2d
    eqeq2d
    cbvrex2v
    @35
    @41
    @27
    vc
    vd
    cz
    cz
    @0
    cA
    @26
    eqeq1
    2rexbidv
    syl5bb
    2rexbidv
    syl5bb
    elab3
    bitri
end
