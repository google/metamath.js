include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "cdiv.mm"
include "cn0.mm"
include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cdvds.mm"
include "cmul.mm"
include "cmin.mm"
include "cn.mm"
include "cv.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "4sqlem13.mm"
include "simpld.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "sseldi.mm"
include "nnzd.mm"
include "cprime.mm"
include "prmz.mm"
include "syl.mm"
include "dvdsmul1.mm"
include "syl2anc.mm"
include "4sqlem8.mm"
include "wa.mm"
include "wi.mm"
include "zsqcl.mm"
include "4sqlem5.mm"
include "zsqcl2.mm"
include "nn0zd.mm"
include "zsubcld.mm"
include "dvds2add.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "zcnd.mm"
include "sqcld.mm"
include "addsub4d.mm"
include "breqtrrd.mm"
include "zaddcld.mm"
include "nn0addcld.mm"
include "oveq1d.mm"
include "addcld.mm"
include "eqtrd.mm"
include "zmulcld.mm"
include "dvds2sub.mm"
include "nncnd.mm"
include "prmnn.mm"
include "mulcld.mm"
include "nncand.mm"
include "breqtrd.mm"
include "wb.mm"
include "nnne0d.mm"
include "dvdsval2.mm"
include "mpbid.mm"
include "nn0red.mm"
include "nn0ge0d.mm"
include "nnred.mm"
include "nngt0d.mm"
include "divge0.mm"
include "syl22anc.mm"
include "elnn0z.mm"
include "sylanbrc.mm"

theorem 4sqlem14
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
  assert |- ( ph -> R e. NN0 )

  proof
    wph
    cR
    cE
    c2
    cexp
    co
    #
    cF
    c2
    cexp
    co
    #
    caddc
    co
    #
    cG
    c2
    cexp
    co
    #
    cH
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
    cM
    cdiv
    co
    #
    cn0
    4sq.r
    wph
    @7
    cz
    wcel
    #
    cc0
    @7
    cle
    wbr
    #
    @7
    cn0
    wcel
    wph
    cM
    @6
    cdvds
    wbr
    #
    @8
    wph
    cM
    cM
    cP
    cmul
    co
    #
    @11
    @6
    cmin
    co
    #
    cmin
    co
    #
    @6
    cdvds
    wph
    cM
    @11
    cdvds
    wbr
    #
    cM
    @12
    cdvds
    wbr
    #
    cM
    @13
    cdvds
    wbr
    #
    wph
    cM
    cz
    wcel
    #
    cP
    cz
    wcel
    #
    @14
    wph
    cM
    wph
    cT
    cn
    cM
    cT
    vi
    cv
    cP
    cmul
    co
    cS
    wcel
    #
    vi
    cn
    crab
    cn
    4sq.6
    @19
    vi
    cn
    ssrab2
    eqsstri
    #
    wph
    cM
    cT
    cr
    clt
    cinf
    #
    cT
    4sq.7
    wph
    cT
    c1
    cuz
    cfv
    #
    wss
    cT
    c0
    wne
    #
    @21
    cT
    wcel
    cT
    cn
    @22
    @20
    nnuz
    sseqtri
    wph
    @23
    cM
    cP
    clt
    wbr
    wph
    vx
    vy
    vz
    vw
    cP
    cS
    cT
    vi
    vn
    cM
    cN
    4sq.1
    4sq.2
    4sq.3
    4sq.4
    4sq.5
    4sq.6
    4sq.7
    4sqlem13
    simpld
    cT
    c1
    infssuzcl
    sylancr
    syl5eqel
    sseldi
    #
    nnzd
    #
    wph
    cP
    cprime
    wcel
    #
    @18
    4sq.4
    cP
    prmz
    syl
    #
    cM
    cP
    dvdsmul1
    syl2anc
    wph
    cM
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
    @2
    cmin
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
    @5
    cmin
    co
    #
    caddc
    co
    #
    @12
    cdvds
    wph
    cM
    @31
    cdvds
    wbr
    #
    cM
    @35
    cdvds
    wbr
    #
    cM
    @36
    cdvds
    wbr
    #
    wph
    cM
    @28
    @0
    cmin
    co
    #
    @29
    @1
    cmin
    co
    #
    caddc
    co
    #
    @31
    cdvds
    wph
    cM
    @40
    cdvds
    wbr
    #
    cM
    @41
    cdvds
    wbr
    #
    cM
    @42
    cdvds
    wbr
    #
    wph
    cA
    cE
    cM
    4sq.a
    @24
    4sq.e
    4sqlem8
    wph
    cB
    cF
    cM
    4sq.b
    @24
    4sq.f
    4sqlem8
    wph
    @17
    @40
    cz
    wcel
    @41
    cz
    wcel
    @43
    @44
    wa
    @45
    wi
    @25
    wph
    @28
    @0
    wph
    cA
    cz
    wcel
    @28
    cz
    wcel
    4sq.a
    cA
    zsqcl
    syl
    #
    wph
    @0
    wph
    cE
    cz
    wcel
    #
    @0
    cn0
    wcel
    wph
    @47
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
    @24
    4sq.e
    4sqlem5
    simpld
    #
    cE
    zsqcl2
    syl
    #
    nn0zd
    zsubcld
    wph
    @29
    @1
    wph
    cB
    cz
    wcel
    @29
    cz
    wcel
    4sq.b
    cB
    zsqcl
    syl
    #
    wph
    @1
    wph
    cF
    cz
    wcel
    #
    @1
    cn0
    wcel
    wph
    @51
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
    @24
    4sq.f
    4sqlem5
    simpld
    #
    cF
    zsqcl2
    syl
    #
    nn0zd
    zsubcld
    cM
    @40
    @41
    dvds2add
    syl3anc
    mp2and
    wph
    @28
    @29
    @0
    @1
    wph
    cA
    wph
    cA
    4sq.a
    zcnd
    sqcld
    #
    wph
    cB
    wph
    cB
    4sq.b
    zcnd
    sqcld
    #
    wph
    cE
    wph
    cE
    @48
    zcnd
    sqcld
    #
    wph
    cF
    wph
    cF
    @52
    zcnd
    sqcld
    #
    addsub4d
    breqtrrd
    wph
    cM
    @32
    @3
    cmin
    co
    #
    @33
    @4
    cmin
    co
    #
    caddc
    co
    #
    @35
    cdvds
    wph
    cM
    @58
    cdvds
    wbr
    #
    cM
    @59
    cdvds
    wbr
    #
    cM
    @60
    cdvds
    wbr
    #
    wph
    cC
    cG
    cM
    4sq.c
    @24
    4sq.g
    4sqlem8
    wph
    cD
    cH
    cM
    4sq.d
    @24
    4sq.h
    4sqlem8
    wph
    @17
    @58
    cz
    wcel
    @59
    cz
    wcel
    @61
    @62
    wa
    @63
    wi
    @25
    wph
    @32
    @3
    wph
    cC
    cz
    wcel
    @32
    cz
    wcel
    4sq.c
    cC
    zsqcl
    syl
    #
    wph
    @3
    wph
    cG
    cz
    wcel
    #
    @3
    cn0
    wcel
    wph
    @65
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
    @24
    4sq.g
    4sqlem5
    simpld
    #
    cG
    zsqcl2
    syl
    #
    nn0zd
    zsubcld
    wph
    @33
    @4
    wph
    cD
    cz
    wcel
    @33
    cz
    wcel
    4sq.d
    cD
    zsqcl
    syl
    #
    wph
    @4
    wph
    cH
    cz
    wcel
    #
    @4
    cn0
    wcel
    wph
    @69
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
    @24
    4sq.h
    4sqlem5
    simpld
    #
    cH
    zsqcl2
    syl
    #
    nn0zd
    zsubcld
    cM
    @58
    @59
    dvds2add
    syl3anc
    mp2and
    wph
    @32
    @33
    @3
    @4
    wph
    cC
    wph
    cC
    4sq.c
    zcnd
    sqcld
    #
    wph
    cD
    wph
    cD
    4sq.d
    zcnd
    sqcld
    #
    wph
    cG
    wph
    cG
    @66
    zcnd
    sqcld
    #
    wph
    cH
    wph
    cH
    @70
    zcnd
    sqcld
    #
    addsub4d
    breqtrrd
    wph
    @17
    @31
    cz
    wcel
    @35
    cz
    wcel
    @37
    @38
    wa
    @39
    wi
    @25
    wph
    @30
    @2
    wph
    @28
    @29
    @46
    @50
    zaddcld
    wph
    @2
    wph
    @0
    @1
    @49
    @53
    nn0addcld
    #
    nn0zd
    #
    zsubcld
    wph
    @34
    @5
    wph
    @32
    @33
    @64
    @68
    zaddcld
    wph
    @5
    wph
    @3
    @4
    @67
    @71
    nn0addcld
    #
    nn0zd
    #
    zsubcld
    cM
    @31
    @35
    dvds2add
    syl3anc
    mp2and
    wph
    @12
    @30
    @34
    caddc
    co
    #
    @6
    cmin
    co
    @36
    wph
    @11
    @80
    @6
    cmin
    4sq.p
    oveq1d
    wph
    @30
    @34
    @2
    @5
    wph
    @28
    @29
    @54
    @55
    addcld
    wph
    @32
    @33
    @72
    @73
    addcld
    wph
    @0
    @1
    @56
    @57
    addcld
    #
    wph
    @3
    @4
    @74
    @75
    addcld
    #
    addsub4d
    eqtrd
    breqtrrd
    wph
    @17
    @11
    cz
    wcel
    @12
    cz
    wcel
    @14
    @15
    wa
    @16
    wi
    @25
    wph
    cM
    cP
    @25
    @27
    zmulcld
    #
    wph
    @11
    @6
    @83
    wph
    @2
    @5
    @77
    @79
    zaddcld
    zsubcld
    cM
    @11
    @12
    dvds2sub
    syl3anc
    mp2and
    wph
    @11
    @6
    wph
    cM
    cP
    wph
    cM
    @24
    nncnd
    wph
    cP
    wph
    @26
    cP
    cn
    wcel
    4sq.4
    cP
    prmnn
    syl
    nncnd
    mulcld
    wph
    @2
    @5
    @81
    @82
    addcld
    nncand
    breqtrd
    wph
    @17
    cM
    cc0
    wne
    @6
    cz
    wcel
    @10
    @8
    wb
    @25
    wph
    cM
    @24
    nnne0d
    wph
    @6
    wph
    @2
    @5
    @76
    @78
    nn0addcld
    #
    nn0zd
    cM
    @6
    dvdsval2
    syl3anc
    mpbid
    wph
    @6
    cr
    wcel
    cc0
    @6
    cle
    wbr
    cM
    cr
    wcel
    cc0
    cM
    clt
    wbr
    @9
    wph
    @6
    @84
    nn0red
    wph
    @6
    @84
    nn0ge0d
    wph
    cM
    @24
    nnred
    wph
    cM
    @24
    nngt0d
    @6
    cM
    divge0
    syl22anc
    @7
    elnn0z
    sylanbrc
    syl5eqel
end
