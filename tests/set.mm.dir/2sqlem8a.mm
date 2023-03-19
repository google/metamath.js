include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "cgcd.mm"
include "co.mm"
include "cn.mm"
include "cmin.mm"
include "cdiv.mm"
include "c1.mm"
include "wne.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "eluz2b3.mm"
include "sylib.mm"
include "simpld.mm"
include "4sqlem5.mm"
include "cexp.mm"
include "simprd.mm"
include "cle.mm"
include "wbr.mm"
include "cdvds.mm"
include "simpr.mm"
include "4sqlem9.mm"
include "ex.mm"
include "wb.mm"
include "eluzelz.mm"
include "syl.mm"
include "dvdssq.mm"
include "syl2anc.mm"
include "sylibrd.mm"
include "wi.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "neneqd.mm"
include "gcdeq0.mm"
include "mtbid.mm"
include "dvdslegcd.mm"
include "syl31anc.mm"
include "syl2and.mm"
include "breq2d.mm"
include "nnle1eq1.mm"
include "bitrd.mm"
include "sylibd.mm"
include "necon3ad.mm"
include "mpd.mm"
include "cc.mm"
include "zcnd.mm"
include "sqeq0.mm"
include "anbi12d.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"

theorem 2sqlem8a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cM: class M
  let cN: class N
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vm: setvar m
  let vu: setvar u
  let vv: setvar v
  let cE: class E
  let cF: class F
  let cP: class P
  assume 2sq.1: |- S = ran ( w e. Z[i] |-> ( ( abs ` w ) ^ 2 ) )
  assume 2sqlem7.2: |- Y = { z | E. x e. ZZ E. y e. ZZ ( ( x gcd y ) = 1 /\ z = ( ( x ^ 2 ) + ( y ^ 2 ) ) ) }
  assume 2sqlem9.5: |- ( ph -> A. b e. ( 1 ... ( M - 1 ) ) A. a e. Y ( b || a -> b e. S ) )
  assume 2sqlem9.7: |- ( ph -> M || N )
  assume 2sqlem8.n: |- ( ph -> N e. NN )
  assume 2sqlem8.m: |- ( ph -> M e. ( ZZ>= ` 2 ) )
  assume 2sqlem8.1: |- ( ph -> A e. ZZ )
  assume 2sqlem8.2: |- ( ph -> B e. ZZ )
  assume 2sqlem8.3: |- ( ph -> ( A gcd B ) = 1 )
  assume 2sqlem8.4: |- ( ph -> N = ( ( A ^ 2 ) + ( B ^ 2 ) ) )
  assume 2sqlem8.c: |- C = ( ( ( A + ( M / 2 ) ) mod M ) - ( M / 2 ) )
  assume 2sqlem8.d: |- D = ( ( ( B + ( M / 2 ) ) mod M ) - ( M / 2 ) )

  disjoint a b
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A a
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint C x
  disjoint ph x
  disjoint ph y
  disjoint B a
  disjoint B b
  disjoint B x
  disjoint B y
  disjoint M a
  disjoint M b
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint S a
  disjoint S b
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint D x
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Y a
  disjoint Y b
  disjoint Y x
  disjoint Y y
  disjoint a n
  disjoint a p
  disjoint a q
  disjoint b n
  disjoint b p
  disjoint b q
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
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
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
  disjoint b m
  disjoint m p
  disjoint B m
  disjoint B p
  disjoint a u
  disjoint a v
  disjoint b u
  disjoint b v
  disjoint M p
  disjoint u z
  disjoint M u
  disjoint v z
  disjoint M v
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
  disjoint E a
  disjoint E p
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint N p
  disjoint N q
  disjoint N u
  disjoint N v
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
  disjoint P x
  disjoint P y
  assert |- ( ph -> ( C gcd D ) e. NN )

  proof
    wph
    cC
    cz
    wcel
    #
    cD
    cz
    wcel
    #
    cC
    cc0
    wceq
    #
    cD
    cc0
    wceq
    #
    wa
    #
    wn
    cC
    cD
    cgcd
    co
    cn
    wcel
    wph
    @0
    cA
    cC
    cmin
    co
    cM
    cdiv
    co
    cz
    wcel
    wph
    cA
    cC
    cM
    2sqlem8.1
    wph
    cM
    cn
    wcel
    #
    cM
    c1
    wne
    #
    wph
    cM
    c2
    cuz
    cfv
    wcel
    #
    @5
    @6
    wa
    2sqlem8.m
    cM
    eluz2b3
    sylib
    #
    simpld
    #
    2sqlem8.c
    4sqlem5
    simpld
    #
    wph
    @1
    cB
    cD
    cmin
    co
    cM
    cdiv
    co
    cz
    wcel
    wph
    cB
    cD
    cM
    2sqlem8.2
    @9
    2sqlem8.d
    4sqlem5
    simpld
    #
    wph
    cC
    c2
    cexp
    co
    cc0
    wceq
    #
    cD
    c2
    cexp
    co
    cc0
    wceq
    #
    wa
    #
    @4
    wph
    @6
    @14
    wn
    wph
    @5
    @6
    @8
    simprd
    wph
    @14
    cM
    c1
    wph
    @14
    cM
    cA
    cB
    cgcd
    co
    #
    cle
    wbr
    #
    cM
    c1
    wceq
    #
    wph
    @12
    cM
    cA
    cdvds
    wbr
    #
    @13
    cM
    cB
    cdvds
    wbr
    #
    @16
    wph
    @12
    cM
    c2
    cexp
    co
    #
    cA
    c2
    cexp
    co
    cdvds
    wbr
    #
    @18
    wph
    @12
    @21
    wph
    @12
    cA
    cC
    cM
    2sqlem8.1
    @9
    2sqlem8.c
    wph
    @12
    simpr
    4sqlem9
    ex
    wph
    cM
    cz
    wcel
    #
    cA
    cz
    wcel
    #
    @18
    @21
    wb
    wph
    @7
    @22
    2sqlem8.m
    c2
    cM
    eluzelz
    syl
    #
    2sqlem8.1
    cM
    cA
    dvdssq
    syl2anc
    sylibrd
    wph
    @13
    @20
    cB
    c2
    cexp
    co
    cdvds
    wbr
    #
    @19
    wph
    @13
    @25
    wph
    @13
    cB
    cD
    cM
    2sqlem8.2
    @9
    2sqlem8.d
    wph
    @13
    simpr
    4sqlem9
    ex
    wph
    @22
    cB
    cz
    wcel
    #
    @19
    @25
    wb
    @24
    2sqlem8.2
    cM
    cB
    dvdssq
    syl2anc
    sylibrd
    wph
    @22
    @23
    @26
    cA
    cc0
    wceq
    cB
    cc0
    wceq
    wa
    #
    wn
    @18
    @19
    wa
    @16
    wi
    @24
    2sqlem8.1
    2sqlem8.2
    wph
    @15
    cc0
    wceq
    #
    @27
    wph
    @15
    cc0
    wph
    @15
    c1
    cc0
    2sqlem8.3
    c1
    cc0
    wne
    wph
    ax-1ne0
    a1i
    eqnetrd
    neneqd
    wph
    @23
    @26
    @28
    @27
    wb
    2sqlem8.1
    2sqlem8.2
    cA
    cB
    gcdeq0
    syl2anc
    mtbid
    cM
    cA
    cB
    dvdslegcd
    syl31anc
    syl2and
    wph
    @16
    cM
    c1
    cle
    wbr
    #
    @17
    wph
    @15
    c1
    cM
    cle
    2sqlem8.3
    breq2d
    wph
    @5
    @29
    @17
    wb
    @9
    cM
    nnle1eq1
    syl
    bitrd
    sylibd
    necon3ad
    mpd
    wph
    @12
    @2
    @13
    @3
    wph
    cC
    cc
    wcel
    @12
    @2
    wb
    wph
    cC
    @10
    zcnd
    cC
    sqeq0
    syl
    wph
    cD
    cc
    wcel
    @13
    @3
    wb
    wph
    cD
    @11
    zcnd
    cD
    sqeq0
    syl
    anbi12d
    mtbid
    cC
    cD
    gcdn0cl
    syl21anc
end
