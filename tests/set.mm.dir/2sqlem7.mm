include "cv.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "wa.mm"
include "cz.mm"
include "wrex.mm"
include "cab.mm"
include "cn.mm"
include "cin.mm"
include "wcel.mm"
include "simpr.mm"
include "reximi.mm"
include "2sqlem2.mm"
include "sylibr.mm"
include "cc0.mm"
include "wn.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "wb.mm"
include "gcdeq0.mm"
include "adantr.mm"
include "eqeq1d.mm"
include "bitr3d.mm"
include "necon3bbid.mm"
include "mpbiri.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "cn0.mm"
include "zsqcl2.mm"
include "ad2antrr.mm"
include "nn0red.mm"
include "nn0ge0d.mm"
include "ad2antlr.mm"
include "add20.mm"
include "syl22anc.mm"
include "cc.mm"
include "zcn.mm"
include "sqeq0.mm"
include "bi2anan9.mm"
include "syl2anc.mm"
include "bitrd.mm"
include "mtbird.mm"
include "wo.mm"
include "nn0addcl.mm"
include "syl2an.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "mt3d.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "rexlimivv.mm"
include "elind.mm"
include "abssi.mm"
include "eqsstri.mm"

theorem 2sqlem7
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
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
  let cP: class P
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
  disjoint P x
  disjoint P y
  assert |- Y C_ ( S i^i NN )

  proof
    cY
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
    vz
    cv
    #
    @0
    c2
    cexp
    co
    #
    @1
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
    #
    vx
    cz
    wrex
    #
    vz
    cab
    cS
    cn
    cin
    #
    2sqlem7.2
    @11
    vz
    @12
    @11
    cS
    cn
    @4
    @11
    @8
    vy
    cz
    wrex
    #
    vx
    cz
    wrex
    @4
    cS
    wcel
    @10
    @13
    vx
    cz
    @9
    @8
    vy
    cz
    @3
    @8
    simpr
    reximi
    reximi
    vx
    vy
    vw
    @4
    cS
    2sq.1
    2sqlem2
    sylibr
    @9
    @4
    cn
    wcel
    #
    vx
    vy
    cz
    cz
    @0
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    wa
    #
    @3
    @8
    @14
    @17
    @3
    wa
    #
    @14
    @8
    @7
    cn
    wcel
    #
    @18
    @19
    @7
    cc0
    wceq
    #
    @18
    @20
    @0
    cc0
    wceq
    #
    @1
    cc0
    wceq
    #
    wa
    #
    @18
    @23
    wn
    c1
    cc0
    wne
    ax-1ne0
    @18
    @23
    c1
    cc0
    @18
    @2
    cc0
    wceq
    #
    @23
    c1
    cc0
    wceq
    @17
    @24
    @23
    wb
    @3
    @0
    @1
    gcdeq0
    adantr
    @18
    @2
    c1
    cc0
    @17
    @3
    simpr
    eqeq1d
    bitr3d
    necon3bbid
    mpbiri
    @18
    @20
    @5
    cc0
    wceq
    #
    @6
    cc0
    wceq
    #
    wa
    #
    @23
    @18
    @5
    cr
    wcel
    cc0
    @5
    cle
    wbr
    @6
    cr
    wcel
    cc0
    @6
    cle
    wbr
    @20
    @27
    wb
    @18
    @5
    @15
    @5
    cn0
    wcel
    #
    @16
    @3
    @0
    zsqcl2
    #
    ad2antrr
    #
    nn0red
    @18
    @5
    @30
    nn0ge0d
    @18
    @6
    @16
    @6
    cn0
    wcel
    #
    @15
    @3
    @1
    zsqcl2
    #
    ad2antlr
    #
    nn0red
    @18
    @6
    @33
    nn0ge0d
    @5
    @6
    add20
    syl22anc
    @18
    @0
    cc
    wcel
    #
    @1
    cc
    wcel
    #
    @27
    @23
    wb
    @15
    @34
    @16
    @3
    @0
    zcn
    ad2antrr
    @16
    @35
    @15
    @3
    @1
    zcn
    ad2antlr
    @34
    @25
    @21
    @35
    @26
    @22
    @0
    sqeq0
    @1
    sqeq0
    bi2anan9
    syl2anc
    bitrd
    mtbird
    @18
    @19
    @20
    @18
    @7
    cn0
    wcel
    #
    @19
    @20
    wo
    @17
    @36
    @3
    @15
    @28
    @31
    @36
    @16
    @29
    @32
    @5
    @6
    nn0addcl
    syl2an
    adantr
    @7
    elnn0
    sylib
    ord
    mt3d
    @4
    @7
    cn
    eleq1
    syl5ibrcom
    expimpd
    rexlimivv
    elind
    abssi
    eqsstri
end
