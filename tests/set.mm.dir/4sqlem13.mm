include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cmul.mm"
include "wceq.mm"
include "cgz.mm"
include "wrex.mm"
include "cmin.mm"
include "cfz.mm"
include "c0.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cmo.mm"
include "cc0.mm"
include "cab.mm"
include "cmpt.mm"
include "eqid.mm"
include "4sqlem12.mm"
include "wcel.mm"
include "cn.mm"
include "simplrl.mm"
include "elfznn.mm"
include "syl.mm"
include "simpr.mm"
include "abs1.mm"
include "oveq1i.mm"
include "sq1.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "simplrr.mm"
include "cz.mm"
include "1z.mm"
include "zgz.mm"
include "ax-mp.mm"
include "4sqlem4a.mm"
include "sylancl.mm"
include "syl5eqelr.mm"
include "eqeltrrd.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "cr.mm"
include "cinf.mm"
include "cuz.mm"
include "wss.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "sseldi.mm"
include "nnred.mm"
include "cprime.mm"
include "ad2antrr.mm"
include "prmnn.mm"
include "cle.mm"
include "infssuzle.mm"
include "syl5eqbr.mm"
include "w3a.mm"
include "wb.mm"
include "prmz.mm"
include "elfzm11.mm"
include "mpbid.mm"
include "simp3d.mm"
include "lelttrd.mm"
include "jca.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem 4sqlem13
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cP: class P
  let cS: class S
  let cT: class T
  let vi: setvar i
  let vn: setvar n
  let cM: class M
  let cN: class N
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
  let cA: class A
  let cC: class C
  let cD: class D
  let cF: class F
  let vu: setvar u
  let vm: setvar m
  let cR: class R
  assume 4sq.1: |- S = { n | E. x e. ZZ E. y e. ZZ E. z e. ZZ E. w e. ZZ n = ( ( ( x ^ 2 ) + ( y ^ 2 ) ) + ( ( z ^ 2 ) + ( w ^ 2 ) ) ) }
  assume 4sq.2: |- ( ph -> N e. NN )
  assume 4sq.3: |- ( ph -> P = ( ( 2 x. N ) + 1 ) )
  assume 4sq.4: |- ( ph -> P e. Prime )
  assume 4sq.5: |- ( ph -> ( 0 ... ( 2 x. N ) ) C_ S )
  assume 4sq.6: |- T = { i e. NN | ( i x. P ) e. S }
  assume 4sq.7: |- M = inf ( T , RR , < )

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
  disjoint i n
  disjoint M i
  disjoint M n
  disjoint N n
  disjoint P i
  disjoint P n
  disjoint n ph
  disjoint S i
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
  disjoint n v
  disjoint A n
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
  disjoint R i
  assert |- ( ph -> ( T =/= (/) /\ M < P ) )

  proof
    wph
    vu
    cv
    #
    cabs
    cfv
    c2
    cexp
    co
    #
    c1
    caddc
    co
    #
    vk
    cv
    #
    cP
    cmul
    co
    #
    wceq
    #
    vu
    cgz
    wrex
    vk
    c1
    cP
    c1
    cmin
    co
    #
    cfz
    co
    #
    wrex
    cT
    c0
    wne
    #
    cM
    cP
    clt
    wbr
    #
    wa
    #
    wph
    vx
    vy
    vz
    vw
    vv
    vu
    @0
    vm
    cv
    c2
    cexp
    co
    cP
    cmo
    co
    wceq
    vm
    cc0
    cN
    cfz
    co
    wrex
    vu
    cab
    #
    cP
    cS
    vk
    vm
    vn
    vv
    @11
    @6
    vv
    cv
    cmin
    co
    cmpt
    #
    cN
    4sq.1
    4sq.2
    4sq.3
    4sq.4
    @11
    eqid
    @12
    eqid
    4sqlem12
    wph
    @5
    @10
    vk
    vu
    @7
    cgz
    wph
    @3
    @7
    wcel
    #
    @0
    cgz
    wcel
    #
    wa
    #
    wa
    #
    @5
    @10
    @16
    @5
    wa
    #
    @8
    @9
    @17
    @3
    cT
    wcel
    #
    @8
    @17
    @3
    cn
    wcel
    #
    @4
    cS
    wcel
    #
    @18
    @17
    @13
    @19
    wph
    @13
    @14
    @5
    simplrl
    #
    @3
    @6
    elfznn
    syl
    #
    @17
    @2
    @4
    cS
    @16
    @5
    simpr
    @17
    @2
    @1
    c1
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
    cS
    @24
    c1
    @1
    caddc
    @24
    c1
    c2
    cexp
    co
    c1
    @23
    c1
    c2
    cexp
    abs1
    oveq1i
    sq1
    eqtri
    oveq2i
    @17
    @14
    c1
    cgz
    wcel
    #
    @25
    cS
    wcel
    wph
    @13
    @14
    @5
    simplrr
    c1
    cz
    wcel
    #
    @26
    1z
    c1
    zgz
    ax-mp
    vx
    vy
    vz
    vw
    @0
    c1
    cS
    vn
    4sq.1
    4sqlem4a
    sylancl
    syl5eqelr
    eqeltrrd
    vi
    cv
    #
    cP
    cmul
    co
    #
    cS
    wcel
    #
    @20
    vi
    @3
    cn
    cT
    @28
    @3
    wceq
    @29
    @4
    cS
    @28
    @3
    cP
    cmul
    oveq1
    eleq1d
    4sq.6
    elrab2
    sylanbrc
    #
    cT
    @3
    ne0i
    syl
    #
    @17
    cM
    @3
    cP
    @17
    cM
    @17
    cT
    cn
    cM
    cT
    @30
    vi
    cn
    crab
    cn
    4sq.6
    @30
    vi
    cn
    ssrab2
    eqsstri
    #
    @17
    cM
    cT
    cr
    clt
    cinf
    #
    cT
    4sq.7
    @17
    cT
    c1
    cuz
    cfv
    #
    wss
    #
    @8
    @34
    cT
    wcel
    cT
    cn
    @35
    @33
    nnuz
    sseqtri
    #
    @32
    cT
    c1
    infssuzcl
    sylancr
    syl5eqel
    sseldi
    nnred
    @17
    @3
    @22
    nnred
    @17
    cP
    @17
    cP
    cprime
    wcel
    #
    cP
    cn
    wcel
    wph
    @38
    @15
    @5
    4sq.4
    ad2antrr
    #
    cP
    prmnn
    syl
    nnred
    @17
    cM
    @34
    @3
    cle
    4sq.7
    @17
    @36
    @18
    @34
    @3
    cle
    wbr
    @37
    @31
    @3
    cT
    c1
    infssuzle
    sylancr
    syl5eqbr
    @17
    @3
    cz
    wcel
    #
    c1
    @3
    cle
    wbr
    #
    @3
    cP
    clt
    wbr
    #
    @17
    @13
    @40
    @41
    @42
    w3a
    #
    @21
    @17
    @27
    cP
    cz
    wcel
    #
    @13
    @43
    wb
    1z
    @17
    @38
    @44
    @39
    cP
    prmz
    syl
    @3
    c1
    cP
    elfzm11
    sylancr
    mpbid
    simp3d
    lelttrd
    jca
    ex
    rexlimdvva
    mpd
end
