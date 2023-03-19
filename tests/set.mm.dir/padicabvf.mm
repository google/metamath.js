include "cprime.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "cq.mm"
include "cc0.mm"
include "wceq.mm"
include "cpc.mm"
include "co.mm"
include "cneg.mm"
include "cexp.mm"
include "cif.mm"
include "cmpt.mm"
include "qex.mm"
include "mptex.mm"
include "fnmpti.mm"
include "c1.mm"
include "cdiv.mm"
include "padicfval.mm"
include "wa.mm"
include "wn.mm"
include "cn.mm"
include "prmnn.mm"
include "ad2antrr.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "wne.mm"
include "cz.mm"
include "df-ne.mm"
include "pcqcl.mm"
include "anassrs.mm"
include "sylan2br.mm"
include "expnegd.mm"
include "exprecd.mm"
include "eqtr4d.mm"
include "ifeq2da.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "cioo.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "nnrecred.mm"
include "nnred.mm"
include "prmgt1.mm"
include "recgt1i.mm"
include "syl2anc.mm"
include "simpld.mm"
include "simprd.mm"
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
include "mpdan.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"

theorem padicabvf
  let vx: setvar x
  let cA: class A
  let cQ: class Q
  let cJ: class J
  let vq: setvar q
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vy: setvar y
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
  let cP: class P
  let cR: class R
  assume qrng.q: |- Q = ( CCfld |`s QQ )
  assume qabsabv.a: |- A = ( AbsVal ` Q )
  assume padic.j: |- J = ( q e. Prime |-> ( x e. QQ |-> if ( x = 0 , 0 , ( q ^ -u ( q pCnt x ) ) ) ) )

  disjoint q x
  disjoint A q
  disjoint A x
  disjoint Q x
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
  disjoint q y
  disjoint q z
  disjoint ph q
  disjoint x y
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
  disjoint A n
  disjoint A p
  disjoint A y
  disjoint A z
  disjoint N k
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Q k
  disjoint Q n
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
  disjoint F n
  disjoint F p
  disjoint F q
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
  assert |- J : Prime --> A

  proof
    cprime
    cA
    cJ
    wf
    cJ
    cprime
    wfn
    vp
    cv
    #
    cJ
    cfv
    #
    cA
    wcel
    #
    vp
    cprime
    wral
    vq
    cprime
    vx
    cq
    vx
    cv
    #
    cc0
    wceq
    #
    cc0
    vq
    cv
    #
    @5
    @3
    cpc
    co
    cneg
    cexp
    co
    cif
    #
    cmpt
    cJ
    vx
    cq
    @6
    qex
    mptex
    padic.j
    fnmpti
    @2
    vp
    cprime
    @0
    cprime
    wcel
    #
    @1
    vx
    cq
    @4
    cc0
    c1
    @0
    cdiv
    co
    #
    @0
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
    @7
    @1
    vx
    cq
    @4
    cc0
    @0
    @9
    cneg
    cexp
    co
    #
    cif
    #
    cmpt
    @12
    vx
    @0
    cJ
    vq
    padic.j
    padicfval
    @7
    vx
    cq
    @14
    @11
    @7
    @3
    cq
    wcel
    #
    wa
    #
    @4
    @13
    @10
    cc0
    @16
    @4
    wn
    #
    wa
    #
    @13
    c1
    @0
    @9
    cexp
    co
    cdiv
    co
    @10
    @18
    @0
    @9
    @18
    @0
    @7
    @0
    cn
    wcel
    @15
    @17
    @0
    prmnn
    #
    ad2antrr
    #
    nncnd
    #
    @18
    @0
    @20
    nnne0d
    #
    @17
    @16
    @3
    cc0
    wne
    #
    @9
    cz
    wcel
    #
    @3
    cc0
    df-ne
    @7
    @15
    @23
    @24
    @0
    @3
    pcqcl
    anassrs
    sylan2br
    #
    expnegd
    @18
    @0
    @9
    @21
    @22
    @25
    exprecd
    eqtr4d
    ifeq2da
    mpteq2dva
    eqtrd
    @7
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
    @7
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
    @26
    @7
    @0
    @19
    nnrecred
    @7
    @28
    @29
    @7
    @0
    cr
    wcel
    c1
    @0
    clt
    wbr
    @28
    @29
    wa
    @7
    @0
    @19
    nnred
    @0
    prmgt1
    @0
    recgt1i
    syl2anc
    #
    simpld
    @7
    @28
    @29
    @30
    simprd
    cc0
    cxr
    wcel
    c1
    cxr
    wcel
    @26
    @27
    @28
    @29
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
    vx
    cA
    @0
    cQ
    @12
    @8
    qrng.q
    qabsabv.a
    @12
    eqid
    padicabv
    mpdan
    eqeltrd
    rgen
    vp
    cprime
    cA
    cJ
    ffnfv
    mpbir2an
end
