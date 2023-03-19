include "cprime.mm"
include "wcel.mm"
include "c4.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "cneg.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "cz.mm"
include "wn.mm"
include "wrex.mm"
include "clgs.mm"
include "simpr.mm"
include "csn.mm"
include "cdif.mm"
include "wb.mm"
include "wne.mm"
include "simpl.mm"
include "1ne2.mm"
include "necomi.mm"
include "oveq1.mm"
include "cr.mm"
include "crp.mm"
include "cc0.mm"
include "cle.mm"
include "clt.mm"
include "2re.mm"
include "4re.mm"
include "4pos.mm"
include "elrpii.mm"
include "0le2.mm"
include "2lt4.mm"
include "modid.mm"
include "mp4an.mm"
include "syl6eq.mm"
include "neeq1d.mm"
include "mpbiri.mm"
include "necon2i.mm"
include "syl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "m1lgs.mm"
include "mpbird.mm"
include "neg1z.mm"
include "lgsqr.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simprd.mm"
include "caddc.mm"
include "cn.mm"
include "cgcd.mm"
include "simprl.mm"
include "1zzd.mm"
include "gcd1.mm"
include "ad2antrl.mm"
include "eqidd.mm"
include "eqeq1d.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "sq1.mm"
include "oveq2d.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "ovex.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "2rexbidv.mm"
include "elab2.mm"
include "sylibr.mm"
include "prmnn.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "cc.mm"
include "zcnd.mm"
include "sqcld.mm"
include "ax-1cn.mm"
include "subneg.mm"
include "sylancl.mm"
include "breqtrd.mm"
include "2sqlem10.mm"
include "syl3anc.mm"
include "rexlimddv.mm"

theorem 2sqlem11
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cP: class P
  let cS: class S
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vm: setvar m
  let cA: class A
  let cC: class C
  let vu: setvar u
  let vv: setvar v
  let wph: wff ph
  let cB: class B
  let cM: class M
  let cD: class D
  let cE: class E
  let cN: class N
  let cF: class F
  assume 2sq.1: |- S = ran ( w e. Z[i] |-> ( ( abs ` w ) ^ 2 ) )
  assume 2sqlem7.2: |- Y = { z | E. x e. ZZ E. y e. ZZ ( ( x gcd y ) = 1 /\ z = ( ( x ^ 2 ) + ( y ^ 2 ) ) ) }

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint Y x
  disjoint Y y
  disjoint P x
  disjoint P y
  disjoint a b
  disjoint a n
  disjoint a p
  disjoint a q
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b n
  disjoint b p
  disjoint b q
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint n p
  disjoint n q
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint p q
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint a m
  disjoint A a
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint C x
  disjoint p u
  disjoint p v
  disjoint p ph
  disjoint q u
  disjoint q v
  disjoint ph q
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint ph u
  disjoint v x
  disjoint v y
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint B a
  disjoint b m
  disjoint B b
  disjoint m p
  disjoint B m
  disjoint B p
  disjoint B x
  disjoint B y
  disjoint a u
  disjoint a v
  disjoint M a
  disjoint b u
  disjoint b v
  disjoint M b
  disjoint M p
  disjoint u z
  disjoint M u
  disjoint v z
  disjoint M v
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint S a
  disjoint S b
  disjoint m n
  disjoint m q
  disjoint m u
  disjoint m v
  disjoint S m
  disjoint n u
  disjoint n v
  disjoint S n
  disjoint S p
  disjoint S q
  disjoint S u
  disjoint S v
  disjoint D x
  disjoint E a
  disjoint E p
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint N p
  disjoint N q
  disjoint N u
  disjoint N v
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Y a
  disjoint Y b
  disjoint Y m
  disjoint Y n
  disjoint F a
  disjoint F p
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint P n
  disjoint P p
  disjoint P q
  assert |- ( ( P e. Prime /\ ( P mod 4 ) = 1 ) -> P e. S )

  proof
    cP
    cprime
    wcel
    #
    cP
    c4
    cmo
    co
    #
    c1
    wceq
    #
    wa
    #
    cP
    vn
    cv
    #
    c2
    cexp
    co
    #
    c1
    cneg
    #
    cmin
    co
    #
    cdvds
    wbr
    #
    cP
    cS
    wcel
    #
    vn
    cz
    @3
    cP
    @6
    cdvds
    wbr
    wn
    #
    @8
    vn
    cz
    wrex
    #
    @3
    @6
    cP
    clgs
    co
    c1
    wceq
    #
    @10
    @11
    wa
    #
    @3
    @12
    @2
    @0
    @2
    simpr
    #
    @3
    cP
    cprime
    c2
    csn
    cdif
    wcel
    #
    @12
    @2
    wb
    @3
    @0
    cP
    c2
    wne
    #
    @15
    @0
    @2
    simpl
    @3
    @2
    @16
    @14
    cP
    c2
    @1
    c1
    cP
    c2
    wceq
    #
    @1
    c1
    wne
    c2
    c1
    wne
    c1
    c2
    1ne2
    necomi
    @17
    @1
    c2
    c1
    @17
    @1
    c2
    c4
    cmo
    co
    #
    c2
    cP
    c2
    c4
    cmo
    oveq1
    c2
    cr
    wcel
    c4
    crp
    wcel
    cc0
    c2
    cle
    wbr
    c2
    c4
    clt
    wbr
    @18
    c2
    wceq
    2re
    c4
    4re
    4pos
    elrpii
    0le2
    2lt4
    c2
    c4
    modid
    mp4an
    syl6eq
    neeq1d
    mpbiri
    necon2i
    syl
    cP
    cprime
    c2
    eldifsn
    sylanbrc
    #
    cP
    m1lgs
    syl
    mpbird
    @3
    @6
    cz
    wcel
    @15
    @12
    @13
    wb
    neg1z
    @19
    vn
    @6
    cP
    lgsqr
    sylancr
    mpbid
    simprd
    @3
    @4
    cz
    wcel
    #
    @8
    wa
    #
    wa
    #
    @5
    c1
    caddc
    co
    #
    cY
    wcel
    #
    cP
    cn
    wcel
    #
    cP
    @23
    cdvds
    wbr
    @9
    @22
    vx
    cv
    #
    vy
    cv
    #
    cgcd
    co
    #
    c1
    wceq
    #
    @23
    @26
    c2
    cexp
    co
    #
    @27
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    #
    wa
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    #
    @24
    @22
    @20
    c1
    cz
    wcel
    @4
    c1
    cgcd
    co
    #
    c1
    wceq
    #
    @23
    @23
    wceq
    #
    @35
    @3
    @20
    @8
    simprl
    #
    @22
    1zzd
    @20
    @37
    @3
    @8
    @4
    gcd1
    ad2antrl
    @22
    @23
    eqidd
    @34
    @37
    @38
    wa
    @4
    @27
    cgcd
    co
    #
    c1
    wceq
    #
    @23
    @5
    @31
    caddc
    co
    #
    wceq
    #
    wa
    vx
    vy
    @4
    c1
    cz
    cz
    @26
    @4
    wceq
    #
    @29
    @41
    @33
    @43
    @44
    @28
    @40
    c1
    @26
    @4
    @27
    cgcd
    oveq1
    eqeq1d
    @44
    @32
    @42
    @23
    @44
    @30
    @5
    @31
    caddc
    @26
    @4
    c2
    cexp
    oveq1
    oveq1d
    eqeq2d
    anbi12d
    @27
    c1
    wceq
    #
    @41
    @37
    @43
    @38
    @45
    @40
    @36
    c1
    @27
    c1
    @4
    cgcd
    oveq2
    eqeq1d
    @45
    @42
    @23
    @23
    @45
    @31
    c1
    @5
    caddc
    @45
    @31
    c1
    c2
    cexp
    co
    c1
    @27
    c1
    c2
    cexp
    oveq1
    sq1
    syl6eq
    oveq2d
    eqeq2d
    anbi12d
    rspc2ev
    syl112anc
    @29
    vz
    cv
    #
    @32
    wceq
    #
    wa
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    @35
    vz
    @23
    cY
    @5
    c1
    caddc
    ovex
    @46
    @23
    wceq
    #
    @48
    @34
    vx
    vy
    cz
    cz
    @49
    @47
    @33
    @29
    @46
    @23
    @32
    eqeq1
    anbi2d
    2rexbidv
    2sqlem7.2
    elab2
    sylibr
    @0
    @25
    @2
    @21
    cP
    prmnn
    ad2antrr
    @22
    cP
    @7
    @23
    cdvds
    @3
    @20
    @8
    simprr
    @22
    @5
    cc
    wcel
    c1
    cc
    wcel
    @7
    @23
    wceq
    @22
    @4
    @22
    @4
    @39
    zcnd
    sqcld
    ax-1cn
    @5
    c1
    subneg
    sylancl
    breqtrd
    vx
    vy
    vz
    vw
    @23
    cP
    cS
    cY
    2sq.1
    2sqlem7.2
    2sqlem10
    syl3anc
    rexlimddv
end
