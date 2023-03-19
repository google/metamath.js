include "cdr.mm"
include "wcel.mm"
include "qdrng.mm"
include "cq.mm"
include "cc0.mm"
include "qrngbas.mm"
include "qrng0.mm"
include "abvtriv.mm"
include "mp1i.mm"
include "cv.mm"
include "cprime.mm"
include "wa.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "r19.21bi.mm"
include "cn.mm"
include "prmnn.mm"
include "sylan2.mm"
include "cr.mm"
include "wb.mm"
include "nnq.mm"
include "syl.mm"
include "abvcl.mm"
include "syl2an.mm"
include "1re.mm"
include "lttri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "adantl.mm"
include "cif.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "c0ex.mm"
include "1ex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "nnne0.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "eqtr4d.mm"
include "ostthlem2.mm"

theorem ostth1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cQ: class Q
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cK: class K
  let vq: setvar q
  let vk: setvar k
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let vj: setvar j
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let cS: class S
  let cT: class T
  let cU: class U
  let cX: class X
  let cN: class N
  let cY: class Y
  let cP: class P
  let cR: class R
  assume qrng.q: |- Q = ( CCfld |`s QQ )
  assume qabsabv.a: |- A = ( AbsVal ` Q )
  assume padic.j: |- J = ( q e. Prime |-> ( x e. QQ |-> if ( x = 0 , 0 , ( q ^ -u ( q pCnt x ) ) ) ) )
  assume ostth.k: |- K = ( x e. QQ |-> if ( x = 0 , 0 , 1 ) )
  assume ostth.1: |- ( ph -> F e. A )
  assume ostth1.2: |- ( ph -> A. n e. NN -. 1 < ( F ` n ) )
  assume ostth1.3: |- ( ph -> A. n e. Prime -. ( F ` n ) < 1 )

  disjoint K n
  disjoint n x
  disjoint n q
  disjoint n ph
  disjoint q x
  disjoint ph q
  disjoint ph x
  disjoint A n
  disjoint A q
  disjoint A x
  disjoint Q n
  disjoint Q x
  disjoint F n
  disjoint F q
  disjoint F x
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
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint M j
  disjoint k x
  disjoint M k
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
  disjoint p q
  disjoint p x
  disjoint p ph
  disjoint q y
  disjoint q z
  disjoint x y
  disjoint x z
  disjoint ph y
  disjoint ph z
  disjoint a g
  disjoint J a
  disjoint g p
  disjoint g y
  disjoint g z
  disjoint J g
  disjoint J p
  disjoint J y
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
  disjoint A p
  disjoint A y
  disjoint A z
  disjoint N k
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Q k
  disjoint Q y
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
  disjoint F p
  disjoint F y
  disjoint F z
  disjoint P a
  disjoint P b
  disjoint P k
  disjoint P p
  disjoint P q
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint R a
  disjoint R p
  disjoint R q
  disjoint R y
  disjoint R z
  assert |- ( ph -> F = K )

  proof
    wph
    cA
    cQ
    cF
    cK
    vn
    qrng.q
    qabsabv.a
    ostth.1
    cQ
    cdr
    wcel
    cK
    cA
    wcel
    wph
    cQ
    qrng.q
    qdrng
    vx
    cA
    cq
    cQ
    cK
    cc0
    qabsabv.a
    cQ
    qrng.q
    qrngbas
    #
    cQ
    qrng.q
    qrng0
    ostth.k
    abvtriv
    mp1i
    wph
    vn
    cv
    #
    cprime
    wcel
    #
    wa
    #
    @1
    cF
    cfv
    #
    c1
    @1
    cK
    cfv
    #
    @3
    @4
    c1
    wceq
    #
    @4
    c1
    clt
    wbr
    wn
    #
    c1
    @4
    clt
    wbr
    wn
    #
    wph
    @7
    vn
    cprime
    ostth1.3
    r19.21bi
    @2
    wph
    @1
    cn
    wcel
    #
    @8
    @1
    prmnn
    #
    wph
    @8
    vn
    cn
    ostth1.2
    r19.21bi
    sylan2
    @3
    @4
    cr
    wcel
    #
    c1
    cr
    wcel
    @6
    @7
    @8
    wa
    wb
    wph
    cF
    cA
    wcel
    @1
    cq
    wcel
    #
    @11
    @2
    ostth.1
    @2
    @9
    @12
    @10
    @1
    nnq
    #
    syl
    cA
    cq
    cQ
    cF
    @1
    qabsabv.a
    @0
    abvcl
    syl2an
    1re
    @4
    c1
    lttri3
    sylancl
    mpbir2and
    @3
    @9
    @5
    c1
    wceq
    @2
    @9
    wph
    @10
    adantl
    @9
    @5
    @1
    cc0
    wceq
    #
    cc0
    c1
    cif
    #
    c1
    @9
    @12
    @5
    @15
    wceq
    @13
    vx
    @1
    vx
    cv
    #
    cc0
    wceq
    #
    cc0
    c1
    cif
    @15
    cq
    cK
    @16
    @1
    wceq
    @17
    @14
    cc0
    c1
    @16
    @1
    cc0
    eqeq1
    ifbid
    ostth.k
    @14
    cc0
    c1
    c0ex
    1ex
    ifex
    fvmpt
    syl
    @9
    @14
    cc0
    c1
    @9
    @1
    cc0
    @1
    nnne0
    neneqd
    iffalsed
    eqtrd
    syl
    eqtr4d
    ostthlem2
end
