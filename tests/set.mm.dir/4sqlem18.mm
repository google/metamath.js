include "c1.mm"
include "cmul.mm"
include "co.mm"
include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "prmnn.mm"
include "syl.mm"
include "nncnd.mm"
include "mulid2d.mm"
include "wceq.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "cexp.mm"
include "caddc.mm"
include "cz.mm"
include "wrex.mm"
include "wn.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "wbr.mm"
include "4sqlem13.mm"
include "simpld.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "elrab2.mm"
include "sylib.mm"
include "simprd.mm"
include "4sqlem2.mm"
include "adantr.mm"
include "wi.mm"
include "w3a.mm"
include "cdiv.mm"
include "cmo.mm"
include "cmin.mm"
include "simp1l.mm"
include "cc0.mm"
include "cfz.mm"
include "simp1r.mm"
include "simp2ll.mm"
include "simp2lr.mm"
include "simp2rl.mm"
include "simp2rr.mm"
include "eqid.mm"
include "simp3.mm"
include "4sqlem17.mm"
include "pm2.21i.mm"
include "3expia.mm"
include "anassrs.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "pm2.01da.mm"
include "wo.mm"
include "elnn1uz2.mm"
include "ord.mm"
include "mt3d.mm"
include "eqeltrrd.mm"
include "simprbi.mm"

theorem 4sqlem18
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
  assert |- ( ph -> P e. S )

  proof
    wph
    c1
    cP
    cmul
    co
    #
    cP
    cS
    wph
    cP
    wph
    cP
    wph
    cP
    cprime
    wcel
    #
    cP
    cn
    wcel
    4sq.4
    cP
    prmnn
    syl
    nncnd
    mulid2d
    wph
    c1
    cT
    wcel
    #
    @0
    cS
    wcel
    #
    wph
    cM
    c1
    cT
    wph
    cM
    c1
    wceq
    #
    cM
    c2
    cuz
    cfv
    wcel
    #
    wph
    @5
    wph
    @5
    wa
    #
    cM
    cP
    cmul
    co
    #
    va
    cv
    #
    c2
    cexp
    co
    vb
    cv
    #
    c2
    cexp
    co
    caddc
    co
    vc
    cv
    #
    c2
    cexp
    co
    vd
    cv
    #
    c2
    cexp
    co
    caddc
    co
    caddc
    co
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
    @5
    wn
    #
    wph
    @14
    @5
    wph
    @7
    cS
    wcel
    #
    @14
    wph
    cM
    cn
    wcel
    #
    @16
    wph
    cM
    cT
    wcel
    @17
    @16
    wa
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
    @18
    cT
    wcel
    cT
    cn
    @19
    cT
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
    vi
    cn
    crab
    cn
    4sq.6
    @23
    vi
    cn
    ssrab2
    eqsstri
    nnuz
    sseqtri
    wph
    @20
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
    #
    @23
    @16
    vi
    cM
    cn
    cT
    @21
    cM
    wceq
    @22
    @7
    cS
    @21
    cM
    cP
    cmul
    oveq1
    eleq1d
    4sq.6
    elrab2
    sylib
    #
    simprd
    vx
    vy
    vz
    vw
    @7
    cS
    vn
    va
    vb
    vc
    vd
    4sq.1
    4sqlem2
    sylib
    adantr
    @6
    @13
    @15
    va
    vb
    cz
    cz
    @6
    @8
    cz
    wcel
    #
    @9
    cz
    wcel
    #
    wa
    #
    wa
    @12
    @15
    vc
    vd
    cz
    cz
    @6
    @28
    @10
    cz
    wcel
    #
    @11
    cz
    wcel
    #
    wa
    #
    @12
    @15
    wi
    @6
    @28
    @31
    wa
    #
    @12
    @15
    @6
    @32
    @12
    w3a
    #
    @15
    @33
    vx
    vy
    vz
    vw
    @8
    @9
    @10
    @11
    cP
    @8
    cM
    c2
    cdiv
    co
    #
    caddc
    co
    cM
    cmo
    co
    @34
    cmin
    co
    #
    c2
    cexp
    co
    @9
    @34
    caddc
    co
    cM
    cmo
    co
    @34
    cmin
    co
    #
    c2
    cexp
    co
    caddc
    co
    @10
    @34
    caddc
    co
    cM
    cmo
    co
    @34
    cmin
    co
    #
    c2
    cexp
    co
    @11
    @34
    caddc
    co
    cM
    cmo
    co
    @34
    cmin
    co
    #
    c2
    cexp
    co
    caddc
    co
    caddc
    co
    cM
    cdiv
    co
    #
    cS
    cT
    vi
    vn
    @35
    @36
    @37
    @38
    cM
    cN
    4sq.1
    @33
    wph
    cN
    cn
    wcel
    wph
    @5
    @32
    @12
    simp1l
    #
    4sq.2
    syl
    @33
    wph
    cP
    c2
    cN
    cmul
    co
    #
    c1
    caddc
    co
    wceq
    @40
    4sq.3
    syl
    @33
    wph
    @1
    @40
    4sq.4
    syl
    @33
    wph
    cc0
    @41
    cfz
    co
    cS
    wss
    @40
    4sq.5
    syl
    4sq.6
    4sq.7
    wph
    @5
    @32
    @12
    simp1r
    @26
    @27
    @31
    @6
    @12
    simp2ll
    @26
    @27
    @31
    @6
    @12
    simp2lr
    @29
    @30
    @28
    @6
    @12
    simp2rl
    @29
    @30
    @28
    @6
    @12
    simp2rr
    @35
    eqid
    @36
    eqid
    @37
    eqid
    @38
    eqid
    @39
    eqid
    @6
    @32
    @12
    simp3
    4sqlem17
    pm2.21i
    3expia
    anassrs
    rexlimdvva
    rexlimdvva
    mpd
    pm2.01da
    wph
    @4
    @5
    wph
    @17
    @4
    @5
    wo
    wph
    @17
    @16
    @25
    simpld
    cM
    elnn1uz2
    sylib
    ord
    mt3d
    @24
    eqeltrrd
    @2
    c1
    cn
    wcel
    @3
    @23
    @3
    vi
    c1
    cn
    cT
    @21
    c1
    wceq
    @22
    @0
    cS
    @21
    c1
    cP
    cmul
    oveq1
    eleq1d
    4sq.6
    elrab2
    simprbi
    syl
    eqeltrrd
end
