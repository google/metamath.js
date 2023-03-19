include "wcel.mm"
include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cgz.mm"
include "wrex.mm"
include "cmul.mm"
include "4sqlem4.mm"
include "wa.mm"
include "reeanv.mm"
include "c1.mm"
include "cdiv.mm"
include "cn0.mm"
include "simpll.mm"
include "gzabssqcl.mm"
include "syl.mm"
include "simprl.mm"
include "nn0addcld.mm"
include "nn0cnd.mm"
include "div1d.mm"
include "simplr.mm"
include "simprr.mm"
include "oveq12d.mm"
include "eqid.mm"
include "cn.mm"
include "1nn.mm"
include "a1i.mm"
include "cmin.mm"
include "cc.mm"
include "gzsubcl.mm"
include "adantr.mm"
include "gzcn.mm"
include "eqeltrd.mm"
include "adantl.mm"
include "mul4sqlem.mm"
include "eqeltrrd.mm"
include "oveq12.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"

theorem mul4sq
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
  assert |- ( ( A e. S /\ B e. S ) -> ( A x. B ) e. S )

  proof
    cA
    cS
    wcel
    cA
    va
    cv
    #
    cabs
    cfv
    c2
    cexp
    co
    #
    vb
    cv
    #
    cabs
    cfv
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    #
    vb
    cgz
    wrex
    #
    va
    cgz
    wrex
    #
    cB
    vc
    cv
    #
    cabs
    cfv
    c2
    cexp
    co
    #
    vd
    cv
    #
    cabs
    cfv
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    #
    vd
    cgz
    wrex
    #
    vc
    cgz
    wrex
    #
    cA
    cB
    cmul
    co
    #
    cS
    wcel
    #
    cB
    cS
    wcel
    vx
    vy
    vz
    vw
    vb
    va
    cA
    cS
    vn
    4sq.1
    4sqlem4
    vx
    vy
    vz
    vw
    vd
    vc
    cB
    cS
    vn
    4sq.1
    4sqlem4
    @7
    @15
    wa
    @6
    @14
    wa
    #
    vc
    cgz
    wrex
    va
    cgz
    wrex
    @17
    @6
    @14
    va
    vc
    cgz
    cgz
    reeanv
    @18
    @17
    va
    vc
    cgz
    cgz
    @18
    @5
    @13
    wa
    #
    vd
    cgz
    wrex
    vb
    cgz
    wrex
    @0
    cgz
    wcel
    #
    @8
    cgz
    wcel
    #
    wa
    #
    @17
    @5
    @13
    vb
    vd
    cgz
    cgz
    reeanv
    @22
    @19
    @17
    vb
    vd
    cgz
    cgz
    @22
    @2
    cgz
    wcel
    #
    @10
    cgz
    wcel
    #
    wa
    #
    wa
    #
    @17
    @19
    @4
    @12
    cmul
    co
    #
    cS
    wcel
    @26
    @4
    c1
    cdiv
    co
    #
    @12
    c1
    cdiv
    co
    #
    cmul
    co
    @27
    cS
    @26
    @28
    @4
    @29
    @12
    cmul
    @26
    @4
    @26
    @4
    @26
    @1
    @3
    @26
    @20
    @1
    cn0
    wcel
    @20
    @21
    @25
    simpll
    #
    @0
    gzabssqcl
    syl
    @26
    @23
    @3
    cn0
    wcel
    @22
    @23
    @24
    simprl
    #
    @2
    gzabssqcl
    syl
    nn0addcld
    #
    nn0cnd
    div1d
    #
    @26
    @12
    @26
    @12
    @26
    @9
    @11
    @26
    @21
    @9
    cn0
    wcel
    @20
    @21
    @25
    simplr
    #
    @8
    gzabssqcl
    syl
    @26
    @24
    @11
    cn0
    wcel
    @22
    @23
    @24
    simprr
    #
    @10
    gzabssqcl
    syl
    nn0addcld
    nn0cnd
    div1d
    oveq12d
    @26
    vx
    vy
    vz
    vw
    @0
    @2
    @8
    @10
    cS
    vn
    c1
    @4
    @12
    4sq.1
    @30
    @31
    @34
    @35
    @4
    eqid
    @12
    eqid
    c1
    cn
    wcel
    @26
    1nn
    a1i
    @26
    @0
    @8
    cmin
    co
    #
    c1
    cdiv
    co
    @36
    cgz
    @26
    @36
    @26
    @36
    cgz
    wcel
    #
    @36
    cc
    wcel
    @22
    @37
    @25
    @0
    @8
    gzsubcl
    adantr
    #
    @36
    gzcn
    syl
    div1d
    @38
    eqeltrd
    @26
    @2
    @10
    cmin
    co
    #
    c1
    cdiv
    co
    @39
    cgz
    @26
    @39
    @26
    @39
    cgz
    wcel
    #
    @39
    cc
    wcel
    @25
    @40
    @22
    @2
    @10
    gzsubcl
    adantl
    #
    @39
    gzcn
    syl
    div1d
    @41
    eqeltrd
    @26
    @28
    @4
    cn0
    @33
    @32
    eqeltrd
    mul4sqlem
    eqeltrrd
    @19
    @16
    @27
    cS
    cA
    @4
    cB
    @12
    cmul
    oveq12
    eleq1d
    syl5ibrcom
    rexlimdvva
    syl5bir
    rexlimivv
    sylbir
    syl2anb
end
