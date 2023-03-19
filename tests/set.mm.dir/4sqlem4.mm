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
include "cz.mm"
include "4sqlem2.mm"
include "wa.mm"
include "ci.mm"
include "cmul.mm"
include "gzreim.mm"
include "adantr.mm"
include "adantl.mm"
include "cre.mm"
include "cim.mm"
include "cc.mm"
include "gzcn.mm"
include "syl.mm"
include "absvalsq2d.mm"
include "cr.mm"
include "zre.mm"
include "crre.mm"
include "syl2an.mm"
include "oveq1d.mm"
include "crim.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "oveqan12d.mm"
include "eqcomd.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "oveq2d.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "wi.mm"
include "4sqlem4a.mm"
include "eleq1a.mm"
include "impbii.mm"

theorem 4sqlem4
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
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
  let cC: class C
  let cD: class D
  let cF: class F
  let vi: setvar i
  let cM: class M
  let vm: setvar m
  let cN: class N
  let cP: class P
  let wph: wff ph
  let cT: class T
  let cR: class R
  assume 4sq.1: |- S = { n | E. x e. ZZ E. y e. ZZ E. z e. ZZ E. w e. ZZ n = ( ( ( x ^ 2 ) + ( y ^ 2 ) ) + ( ( z ^ 2 ) + ( w ^ 2 ) ) ) }

  disjoint A u
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
  disjoint n v
  disjoint A n
  disjoint A v
  disjoint n u
  disjoint u v
  disjoint S n
  disjoint S u
  disjoint S v
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
  disjoint B n
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
  disjoint M n
  disjoint M u
  disjoint k m
  disjoint N k
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint N m
  disjoint N n
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
  disjoint T k
  disjoint T u
  disjoint R i
  assert |- ( A e. S <-> E. u e. Z[i] E. v e. Z[i] A = ( ( ( abs ` u ) ^ 2 ) + ( ( abs ` v ) ^ 2 ) ) )

  proof
    cA
    cS
    wcel
    #
    cA
    vu
    cv
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    vv
    cv
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    #
    vv
    cgz
    wrex
    vu
    cgz
    wrex
    #
    @0
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
    @9
    vx
    vy
    vz
    vw
    cA
    cS
    vn
    va
    vb
    vc
    vd
    4sq.1
    4sqlem2
    @22
    @9
    va
    vb
    cz
    cz
    @10
    cz
    wcel
    #
    @12
    cz
    wcel
    #
    wa
    #
    @21
    @9
    vc
    vd
    cz
    cz
    @25
    @15
    cz
    wcel
    #
    @17
    cz
    wcel
    #
    wa
    #
    wa
    #
    @9
    @21
    @20
    @7
    wceq
    #
    vv
    cgz
    wrex
    vu
    cgz
    wrex
    #
    @29
    @10
    ci
    @12
    cmul
    co
    caddc
    co
    #
    cgz
    wcel
    #
    @15
    ci
    @17
    cmul
    co
    caddc
    co
    #
    cgz
    wcel
    #
    @20
    @32
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    @34
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    #
    @31
    @25
    @33
    @28
    @10
    @12
    gzreim
    #
    adantr
    @28
    @35
    @25
    @15
    @17
    gzreim
    #
    adantl
    @29
    @40
    @20
    @25
    @28
    @37
    @14
    @39
    @19
    caddc
    @25
    @37
    @32
    cre
    cfv
    #
    c2
    cexp
    co
    #
    @32
    cim
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    @14
    @25
    @32
    @25
    @33
    @32
    cc
    wcel
    @42
    @32
    gzcn
    syl
    absvalsq2d
    @25
    @45
    @11
    @47
    @13
    caddc
    @25
    @44
    @10
    c2
    cexp
    @23
    @10
    cr
    wcel
    #
    @12
    cr
    wcel
    #
    @44
    @10
    wceq
    @24
    @10
    zre
    #
    @12
    zre
    #
    @10
    @12
    crre
    syl2an
    oveq1d
    @25
    @46
    @12
    c2
    cexp
    @23
    @48
    @49
    @46
    @12
    wceq
    @24
    @50
    @51
    @10
    @12
    crim
    syl2an
    oveq1d
    oveq12d
    eqtrd
    @28
    @39
    @34
    cre
    cfv
    #
    c2
    cexp
    co
    #
    @34
    cim
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    @19
    @28
    @34
    @28
    @35
    @34
    cc
    wcel
    @43
    @34
    gzcn
    syl
    absvalsq2d
    @28
    @53
    @16
    @55
    @18
    caddc
    @28
    @52
    @15
    c2
    cexp
    @26
    @15
    cr
    wcel
    #
    @17
    cr
    wcel
    #
    @52
    @15
    wceq
    @27
    @15
    zre
    #
    @17
    zre
    #
    @15
    @17
    crre
    syl2an
    oveq1d
    @28
    @54
    @17
    c2
    cexp
    @26
    @56
    @57
    @54
    @17
    wceq
    @27
    @58
    @59
    @15
    @17
    crim
    syl2an
    oveq1d
    oveq12d
    eqtrd
    oveqan12d
    eqcomd
    @30
    @41
    @20
    @37
    @6
    caddc
    co
    #
    wceq
    vu
    vv
    @32
    @34
    cgz
    cgz
    @1
    @32
    wceq
    #
    @7
    @60
    @20
    @61
    @3
    @37
    @6
    caddc
    @61
    @2
    @36
    c2
    cexp
    @1
    @32
    cabs
    fveq2
    oveq1d
    oveq1d
    eqeq2d
    @4
    @34
    wceq
    #
    @60
    @40
    @20
    @62
    @6
    @39
    @37
    caddc
    @62
    @5
    @38
    c2
    cexp
    @4
    @34
    cabs
    fveq2
    oveq1d
    oveq2d
    eqeq2d
    rspc2ev
    syl3anc
    @21
    @8
    @30
    vu
    vv
    cgz
    cgz
    cA
    @20
    @7
    eqeq1
    2rexbidv
    syl5ibrcom
    rexlimdvva
    rexlimivv
    sylbi
    @8
    @0
    vu
    vv
    cgz
    cgz
    @1
    cgz
    wcel
    @4
    cgz
    wcel
    wa
    @7
    cS
    wcel
    @8
    @0
    wi
    vx
    vy
    vz
    vw
    @1
    @4
    cS
    vn
    4sq.1
    4sqlem4a
    @7
    cS
    cA
    eleq1a
    syl
    rexlimivv
    impbii
end
