include "wceq.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cmin.mm"
include "cc0.mm"
include "caddc.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "eluz2nn.mm"
include "syl.mm"
include "nnred.mm"
include "resqcld.mm"
include "rehalfcld.mm"
include "recnd.mm"
include "cz.mm"
include "4sqlem5.mm"
include "simpld.mm"
include "zsqcl.mm"
include "zred.mm"
include "addsub4d.mm"
include "2halvesd.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "adantr.mm"
include "cmul.mm"
include "sqvald.mm"
include "simpr.mm"
include "syl5eqr.mm"
include "readdcld.mm"
include "nnne0d.mm"
include "divcan1d.mm"
include "3eqtr2rd.mm"
include "oveq12d.mm"
include "subidd.mm"
include "3eqtr3d.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "resubcld.mm"
include "4sqlem7.mm"
include "le2addd.mm"
include "breqtrd.mm"
include "subge0d.mm"
include "mpbird.mm"
include "add20.mm"
include "syl22anc.mm"
include "biimpa.mm"
include "syldan.mm"
include "eqtrd.mm"
include "simprd.mm"
include "jca.mm"

theorem 4sqlem15
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let vi: setvar i
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vk: setvar k
  let vv: setvar v
  let vu: setvar u
  let vm: setvar m
  assume 4sq.1: |- S = { n | E. x e. ZZ E. y e. ZZ E. z e. ZZ E. w e. ZZ n = ( ( ( x ^ 2 ) + ( y ^ 2 ) ) + ( ( z ^ 2 ) + ( w ^ 2 ) ) ) }
  assume 4sq.2: |- ( ph -> N e. NN )
  assume 4sq.3: |- ( ph -> P = ( ( 2 x. N ) + 1 ) )
  assume 4sq.4: |- ( ph -> P e. Prime )
  assume 4sq.5: |- ( ph -> ( 0 ... ( 2 x. N ) ) C_ S )
  assume 4sq.6: |- T = { i e. NN | ( i x. P ) e. S }
  assume 4sq.7: |- M = inf ( T , RR , < )
  assume 4sq.m: |- ( ph -> M e. ( ZZ>= ` 2 ) )
  assume 4sq.a: |- ( ph -> A e. ZZ )
  assume 4sq.b: |- ( ph -> B e. ZZ )
  assume 4sq.c: |- ( ph -> C e. ZZ )
  assume 4sq.d: |- ( ph -> D e. ZZ )
  assume 4sq.e: |- E = ( ( ( A + ( M / 2 ) ) mod M ) - ( M / 2 ) )
  assume 4sq.f: |- F = ( ( ( B + ( M / 2 ) ) mod M ) - ( M / 2 ) )
  assume 4sq.g: |- G = ( ( ( C + ( M / 2 ) ) mod M ) - ( M / 2 ) )
  assume 4sq.h: |- H = ( ( ( D + ( M / 2 ) ) mod M ) - ( M / 2 ) )
  assume 4sq.r: |- R = ( ( ( ( E ^ 2 ) + ( F ^ 2 ) ) + ( ( G ^ 2 ) + ( H ^ 2 ) ) ) / M )
  assume 4sq.p: |- ( ph -> ( M x. P ) = ( ( ( A ^ 2 ) + ( B ^ 2 ) ) + ( ( C ^ 2 ) + ( D ^ 2 ) ) ) )

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
  disjoint E n
  disjoint G n
  disjoint H n
  disjoint A n
  disjoint C n
  disjoint D n
  disjoint F n
  disjoint i n
  disjoint M i
  disjoint M n
  disjoint N n
  disjoint P i
  disjoint P n
  disjoint n ph
  disjoint S i
  disjoint S n
  disjoint R i
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
  disjoint i u
  disjoint k u
  disjoint M k
  disjoint n u
  disjoint M u
  disjoint k m
  disjoint N k
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint N m
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
  disjoint j m
  disjoint j u
  disjoint P j
  disjoint P k
  disjoint P m
  disjoint P u
  disjoint P v
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph u
  disjoint ph v
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S u
  disjoint S v
  disjoint T k
  disjoint T u
  assert |- ( ( ph /\ R = M ) -> ( ( ( ( ( ( M ^ 2 ) / 2 ) / 2 ) - ( E ^ 2 ) ) = 0 /\ ( ( ( ( M ^ 2 ) / 2 ) / 2 ) - ( F ^ 2 ) ) = 0 ) /\ ( ( ( ( ( M ^ 2 ) / 2 ) / 2 ) - ( G ^ 2 ) ) = 0 /\ ( ( ( ( M ^ 2 ) / 2 ) / 2 ) - ( H ^ 2 ) ) = 0 ) ) )

  proof
    wph
    cR
    cM
    wceq
    #
    wa
    #
    cM
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    c2
    cdiv
    co
    #
    cE
    c2
    cexp
    co
    #
    cmin
    co
    #
    cc0
    wceq
    @4
    cF
    c2
    cexp
    co
    #
    cmin
    co
    #
    cc0
    wceq
    wa
    #
    @4
    cG
    c2
    cexp
    co
    #
    cmin
    co
    #
    cc0
    wceq
    @4
    cH
    c2
    cexp
    co
    #
    cmin
    co
    #
    cc0
    wceq
    wa
    #
    wph
    @0
    @6
    @8
    caddc
    co
    #
    cc0
    wceq
    #
    @9
    @1
    @15
    @3
    @5
    @7
    caddc
    co
    #
    cmin
    co
    #
    cc0
    wph
    @15
    @18
    wceq
    @0
    wph
    @4
    @4
    caddc
    co
    #
    @17
    cmin
    co
    @15
    @18
    wph
    @4
    @4
    @5
    @7
    wph
    @4
    wph
    @3
    wph
    @2
    wph
    cM
    wph
    cM
    wph
    cM
    c2
    cuz
    cfv
    wcel
    cM
    cn
    wcel
    4sq.m
    cM
    eluz2nn
    syl
    #
    nnred
    #
    resqcld
    #
    rehalfcld
    #
    rehalfcld
    #
    recnd
    #
    @25
    wph
    @5
    wph
    @5
    wph
    cE
    cz
    wcel
    #
    @5
    cz
    wcel
    wph
    @26
    cA
    cE
    cmin
    co
    cM
    cdiv
    co
    cz
    wcel
    wph
    cA
    cE
    cM
    4sq.a
    @20
    4sq.e
    4sqlem5
    simpld
    cE
    zsqcl
    syl
    zred
    #
    recnd
    wph
    @7
    wph
    @7
    wph
    cF
    cz
    wcel
    #
    @7
    cz
    wcel
    wph
    @28
    cB
    cF
    cmin
    co
    cM
    cdiv
    co
    cz
    wcel
    wph
    cB
    cF
    cM
    4sq.b
    @20
    4sq.f
    4sqlem5
    simpld
    cF
    zsqcl
    syl
    zred
    #
    recnd
    addsub4d
    wph
    @19
    @3
    @17
    cmin
    wph
    @3
    wph
    @3
    @23
    recnd
    #
    2halvesd
    #
    oveq1d
    eqtr3d
    adantr
    @1
    @18
    cc0
    wceq
    #
    @3
    @10
    @12
    caddc
    co
    #
    cmin
    co
    #
    cc0
    wceq
    #
    wph
    @0
    @18
    @34
    caddc
    co
    #
    cc0
    wceq
    #
    @32
    @35
    wa
    #
    @1
    @3
    @3
    caddc
    co
    #
    @17
    @33
    caddc
    co
    #
    cmin
    co
    #
    @2
    @2
    cmin
    co
    #
    @36
    cc0
    @1
    @39
    @2
    @40
    @2
    cmin
    wph
    @39
    @2
    wceq
    @0
    wph
    @2
    wph
    @2
    @22
    recnd
    #
    2halvesd
    adantr
    @1
    @2
    cM
    cM
    cmul
    co
    #
    @40
    cM
    cdiv
    co
    #
    cM
    cmul
    co
    #
    @40
    wph
    @2
    @44
    wceq
    @0
    wph
    cM
    wph
    cM
    @21
    recnd
    #
    sqvald
    adantr
    @1
    @45
    cM
    cM
    cmul
    @1
    @45
    cR
    cM
    4sq.r
    wph
    @0
    simpr
    syl5eqr
    oveq1d
    wph
    @46
    @40
    wceq
    @0
    wph
    @40
    cM
    wph
    @40
    wph
    @17
    @33
    wph
    @5
    @7
    @27
    @29
    readdcld
    #
    wph
    @10
    @12
    wph
    @10
    wph
    cG
    cz
    wcel
    #
    @10
    cz
    wcel
    wph
    @49
    cC
    cG
    cmin
    co
    cM
    cdiv
    co
    cz
    wcel
    wph
    cC
    cG
    cM
    4sq.c
    @20
    4sq.g
    4sqlem5
    simpld
    cG
    zsqcl
    syl
    zred
    #
    wph
    @12
    wph
    cH
    cz
    wcel
    #
    @12
    cz
    wcel
    wph
    @51
    cD
    cH
    cmin
    co
    cM
    cdiv
    co
    cz
    wcel
    wph
    cD
    cH
    cM
    4sq.d
    @20
    4sq.h
    4sqlem5
    simpld
    cH
    zsqcl
    syl
    zred
    #
    readdcld
    #
    readdcld
    recnd
    @47
    wph
    cM
    @20
    nnne0d
    divcan1d
    adantr
    3eqtr2rd
    oveq12d
    wph
    @41
    @36
    wceq
    @0
    wph
    @3
    @3
    @17
    @33
    @30
    @30
    wph
    @17
    @48
    recnd
    wph
    @33
    @53
    recnd
    addsub4d
    adantr
    wph
    @42
    cc0
    wceq
    @0
    wph
    @2
    @43
    subidd
    adantr
    3eqtr3d
    wph
    @37
    @38
    wph
    @18
    cr
    wcel
    cc0
    @18
    cle
    wbr
    #
    @34
    cr
    wcel
    cc0
    @34
    cle
    wbr
    #
    @37
    @38
    wb
    wph
    @3
    @17
    @23
    @48
    resubcld
    wph
    @54
    @17
    @3
    cle
    wbr
    wph
    @17
    @19
    @3
    cle
    wph
    @5
    @7
    @4
    @4
    @27
    @29
    @24
    @24
    wph
    cA
    cE
    cM
    4sq.a
    @20
    4sq.e
    4sqlem7
    #
    wph
    cB
    cF
    cM
    4sq.b
    @20
    4sq.f
    4sqlem7
    #
    le2addd
    @31
    breqtrd
    wph
    @3
    @17
    @23
    @48
    subge0d
    mpbird
    wph
    @3
    @33
    @23
    @53
    resubcld
    wph
    @55
    @33
    @3
    cle
    wbr
    wph
    @33
    @19
    @3
    cle
    wph
    @10
    @12
    @4
    @4
    @50
    @52
    @24
    @24
    wph
    cC
    cG
    cM
    4sq.c
    @20
    4sq.g
    4sqlem7
    #
    wph
    cD
    cH
    cM
    4sq.d
    @20
    4sq.h
    4sqlem7
    #
    le2addd
    @31
    breqtrd
    wph
    @3
    @33
    @23
    @53
    subge0d
    mpbird
    @18
    @34
    add20
    syl22anc
    biimpa
    syldan
    #
    simpld
    eqtrd
    wph
    @16
    @9
    wph
    @6
    cr
    wcel
    cc0
    @6
    cle
    wbr
    #
    @8
    cr
    wcel
    cc0
    @8
    cle
    wbr
    #
    @16
    @9
    wb
    wph
    @4
    @5
    @24
    @27
    resubcld
    wph
    @61
    @5
    @4
    cle
    wbr
    @56
    wph
    @4
    @5
    @24
    @27
    subge0d
    mpbird
    wph
    @4
    @7
    @24
    @29
    resubcld
    wph
    @62
    @7
    @4
    cle
    wbr
    @57
    wph
    @4
    @7
    @24
    @29
    subge0d
    mpbird
    @6
    @8
    add20
    syl22anc
    biimpa
    syldan
    wph
    @0
    @11
    @13
    caddc
    co
    #
    cc0
    wceq
    #
    @14
    @1
    @63
    @34
    cc0
    wph
    @63
    @34
    wceq
    @0
    wph
    @19
    @33
    cmin
    co
    @63
    @34
    wph
    @4
    @4
    @10
    @12
    @25
    @25
    wph
    @10
    @50
    recnd
    wph
    @12
    @52
    recnd
    addsub4d
    wph
    @19
    @3
    @33
    cmin
    @31
    oveq1d
    eqtr3d
    adantr
    @1
    @32
    @35
    @60
    simprd
    eqtrd
    wph
    @64
    @14
    wph
    @11
    cr
    wcel
    cc0
    @11
    cle
    wbr
    #
    @13
    cr
    wcel
    cc0
    @13
    cle
    wbr
    #
    @64
    @14
    wb
    wph
    @4
    @10
    @24
    @50
    resubcld
    wph
    @65
    @10
    @4
    cle
    wbr
    @58
    wph
    @4
    @10
    @24
    @50
    subge0d
    mpbird
    wph
    @4
    @12
    @24
    @52
    resubcld
    wph
    @66
    @12
    @4
    cle
    wbr
    @59
    wph
    @4
    @12
    @24
    @52
    subge0d
    mpbird
    @11
    @13
    add20
    syl22anc
    biimpa
    syldan
    jca
end
