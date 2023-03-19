include "cprime.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cq.mm"
include "cv.mm"
include "cfv.mm"
include "ccxp.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "wceq.mm"
include "cneg.mm"
include "cpc.mm"
include "cexp.mm"
include "cif.mm"
include "padicval.mm"
include "adantlr.mm"
include "oveq1d.mm"
include "ovif.mm"
include "cr.mm"
include "rpre.mm"
include "adantl.mm"
include "recnd.mm"
include "wne.mm"
include "rpne0.mm"
include "0cxpd.mm"
include "adantr.mm"
include "ifeq1d.mm"
include "syl5eq.mm"
include "wn.mm"
include "df-ne.mm"
include "cmul.mm"
include "cc.mm"
include "cz.mm"
include "pcqcl.mm"
include "zcnd.mm"
include "mulneg12.mm"
include "syl2anc.mm"
include "negcld.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "cn.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "cuz.mm"
include "prmuz2.mm"
include "eluz2b2.mm"
include "sylib.mm"
include "simpld.mm"
include "nnrpd.mm"
include "znegcld.mm"
include "zred.mm"
include "cxpmuld.mm"
include "renegcld.mm"
include "3eqtr3d.mm"
include "nnred.mm"
include "nnne0d.mm"
include "cxpexpzd.mm"
include "rpcxpcld.mm"
include "rpcnd.mm"
include "syl.mm"
include "anassrs.mm"
include "sylan2br.mm"
include "ifeq2da.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"
include "cioo.mm"
include "rpgt0.mm"
include "lt0neg2d.mm"
include "mpbid.mm"
include "simprd.mm"
include "0red.mm"
include "cxpltd.mm"
include "cxp0d.mm"
include "breqtrd.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "1re.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "eqid.mm"
include "padicabv.mm"
include "syldan.mm"
include "eqeltrd.mm"

theorem padicabvcxp
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cJ: class J
  let vq: setvar q
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vz: setvar z
  let cG: class G
  let cK: class K
  let vj: setvar j
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let wph: wff ph
  let vg: setvar g
  let cS: class S
  let cT: class T
  let cU: class U
  let cX: class X
  let cN: class N
  let cY: class Y
  let cF: class F
  assume qrng.q: |- Q = ( CCfld |`s QQ )
  assume qabsabv.a: |- A = ( AbsVal ` Q )
  assume padic.j: |- J = ( q e. Prime |-> ( x e. QQ |-> if ( x = 0 , 0 , ( q ^ -u ( q pCnt x ) ) ) ) )

  disjoint q x
  disjoint q y
  disjoint x y
  disjoint J y
  disjoint A q
  disjoint A x
  disjoint A y
  disjoint Q x
  disjoint Q y
  disjoint P q
  disjoint P x
  disjoint P y
  disjoint R q
  disjoint R y
  disjoint k n
  disjoint k p
  disjoint k y
  disjoint k z
  disjoint G k
  disjoint n p
  disjoint n y
  disjoint n z
  disjoint G n
  disjoint p y
  disjoint p z
  disjoint G p
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint K k
  disjoint K n
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint M j
  disjoint k x
  disjoint M k
  disjoint n x
  disjoint M n
  disjoint M x
  disjoint a b
  disjoint a k
  disjoint a n
  disjoint a p
  disjoint a q
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a ph
  disjoint b k
  disjoint b n
  disjoint b p
  disjoint b q
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint b ph
  disjoint k q
  disjoint k ph
  disjoint n q
  disjoint n ph
  disjoint p q
  disjoint p x
  disjoint p ph
  disjoint q z
  disjoint ph q
  disjoint x z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint a g
  disjoint J a
  disjoint g p
  disjoint g y
  disjoint g z
  disjoint J g
  disjoint J p
  disjoint J z
  disjoint S a
  disjoint S b
  disjoint S k
  disjoint T j
  disjoint T k
  disjoint T n
  disjoint T x
  disjoint U n
  disjoint U x
  disjoint X k
  disjoint X x
  disjoint A a
  disjoint A k
  disjoint A n
  disjoint A p
  disjoint A z
  disjoint N k
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Q k
  disjoint Q n
  disjoint Q z
  disjoint Y k
  disjoint a j
  disjoint F a
  disjoint b g
  disjoint b j
  disjoint F b
  disjoint g j
  disjoint g k
  disjoint g n
  disjoint g q
  disjoint F g
  disjoint j p
  disjoint j q
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint F k
  disjoint F n
  disjoint F p
  disjoint F q
  disjoint F y
  disjoint F z
  disjoint P a
  disjoint P b
  disjoint P k
  disjoint P p
  disjoint P z
  disjoint R a
  disjoint R p
  disjoint R z
  assert |- ( ( P e. Prime /\ R e. RR+ ) -> ( y e. QQ |-> ( ( ( J ` P ) ` y ) ^c R ) ) e. A )

  proof
    cP
    cprime
    wcel
    #
    cR
    crp
    wcel
    #
    wa
    #
    vy
    cq
    vy
    cv
    #
    cP
    cJ
    cfv
    cfv
    #
    cR
    ccxp
    co
    #
    cmpt
    vy
    cq
    @3
    cc0
    wceq
    #
    cc0
    cP
    cR
    cneg
    #
    ccxp
    co
    #
    cP
    @3
    cpc
    co
    #
    cexp
    co
    #
    cif
    #
    cmpt
    #
    cA
    @2
    vy
    cq
    @5
    @11
    @2
    @3
    cq
    wcel
    #
    wa
    #
    @5
    @6
    cc0
    cP
    @9
    cneg
    #
    cexp
    co
    #
    cif
    #
    cR
    ccxp
    co
    #
    @6
    cc0
    @16
    cR
    ccxp
    co
    #
    cif
    #
    @11
    @14
    @4
    @17
    cR
    ccxp
    @0
    @13
    @4
    @17
    wceq
    @1
    vx
    cP
    cJ
    @3
    vq
    padic.j
    padicval
    adantlr
    oveq1d
    @14
    @18
    @6
    cc0
    cR
    ccxp
    co
    #
    @19
    cif
    @20
    @6
    cc0
    @16
    cR
    ccxp
    ovif
    @14
    @6
    @21
    cc0
    @19
    @2
    @21
    cc0
    wceq
    @13
    @2
    cR
    @2
    cR
    @1
    cR
    cr
    wcel
    @0
    cR
    rpre
    adantl
    #
    recnd
    #
    @1
    cR
    cc0
    wne
    @0
    cR
    rpne0
    adantl
    0cxpd
    adantr
    ifeq1d
    syl5eq
    @14
    @6
    @19
    @10
    cc0
    @6
    wn
    @14
    @3
    cc0
    wne
    #
    @19
    @10
    wceq
    #
    @3
    cc0
    df-ne
    @2
    @13
    @24
    @25
    @2
    @13
    @24
    wa
    #
    wa
    #
    cP
    @15
    ccxp
    co
    #
    cR
    ccxp
    co
    #
    @8
    @9
    ccxp
    co
    #
    @19
    @10
    @27
    cP
    @15
    cR
    cmul
    co
    #
    ccxp
    co
    cP
    @7
    @9
    cmul
    co
    #
    ccxp
    co
    @29
    @30
    @27
    @31
    @32
    cP
    ccxp
    @27
    @31
    @9
    @7
    cmul
    co
    #
    @32
    @27
    @9
    cc
    wcel
    cR
    cc
    wcel
    #
    @31
    @33
    wceq
    @27
    @9
    @0
    @26
    @9
    cz
    wcel
    @1
    cP
    @3
    pcqcl
    adantlr
    #
    zcnd
    #
    @2
    @34
    @26
    @23
    adantr
    #
    @9
    cR
    mulneg12
    syl2anc
    @27
    @9
    @7
    @36
    @27
    cR
    @37
    negcld
    mulcomd
    eqtrd
    oveq2d
    @27
    cP
    @15
    cR
    @2
    cP
    crp
    wcel
    @26
    @2
    cP
    @2
    cP
    cn
    wcel
    #
    c1
    cP
    clt
    wbr
    #
    @2
    cP
    c2
    cuz
    cfv
    wcel
    #
    @38
    @39
    wa
    @0
    @40
    @1
    cP
    prmuz2
    adantr
    cP
    eluz2b2
    sylib
    #
    simpld
    #
    nnrpd
    #
    adantr
    #
    @27
    @15
    @27
    @9
    @35
    znegcld
    #
    zred
    @37
    cxpmuld
    @27
    cP
    @7
    @9
    @44
    @2
    @7
    cr
    wcel
    @26
    @2
    cR
    @22
    renegcld
    #
    adantr
    @36
    cxpmuld
    3eqtr3d
    @27
    @28
    @16
    cR
    ccxp
    @27
    cP
    @15
    @2
    cP
    cc
    wcel
    @26
    @2
    cP
    @2
    cP
    @42
    nnred
    #
    recnd
    #
    adantr
    @2
    cP
    cc0
    wne
    @26
    @2
    cP
    @42
    nnne0d
    adantr
    @45
    cxpexpzd
    oveq1d
    @27
    @8
    @9
    @27
    @8
    @2
    @8
    crp
    wcel
    #
    @26
    @2
    cP
    @7
    @43
    @46
    rpcxpcld
    #
    adantr
    #
    rpcnd
    @27
    @49
    @8
    cc0
    wne
    @51
    @8
    rpne0
    syl
    @35
    cxpexpzd
    3eqtr3d
    anassrs
    sylan2br
    ifeq2da
    3eqtrd
    mpteq2dva
    @0
    @1
    @8
    cc0
    c1
    cioo
    co
    wcel
    #
    @12
    cA
    wcel
    @2
    @8
    cr
    wcel
    #
    cc0
    @8
    clt
    wbr
    #
    @8
    c1
    clt
    wbr
    #
    @52
    @2
    @49
    @53
    @50
    @8
    rpre
    syl
    @2
    @49
    @54
    @50
    @8
    rpgt0
    syl
    @2
    @8
    cP
    cc0
    ccxp
    co
    #
    c1
    clt
    @2
    @7
    cc0
    clt
    wbr
    #
    @8
    @56
    clt
    wbr
    @2
    cc0
    cR
    clt
    wbr
    #
    @57
    @1
    @58
    @0
    cR
    rpgt0
    adantl
    @2
    cR
    @22
    lt0neg2d
    mpbid
    @2
    cP
    @7
    cc0
    @47
    @2
    @38
    @39
    @41
    simprd
    @46
    @2
    0red
    cxpltd
    mpbid
    @2
    cP
    @48
    cxp0d
    breqtrd
    cc0
    cxr
    wcel
    c1
    cxr
    wcel
    @52
    @53
    @54
    @55
    w3a
    wb
    0xr
    c1
    1re
    rexri
    cc0
    c1
    @8
    elioo2
    mp2an
    syl3anbrc
    vy
    cA
    cP
    cQ
    @12
    @8
    qrng.q
    qabsabv.a
    @12
    eqid
    padicabv
    syldan
    eqeltrd
end
