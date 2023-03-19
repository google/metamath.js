include "wcel.mm"
include "cq.mm"
include "cn0.mm"
include "cexp.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "qrng1.mm"
include "qrng0.mm"
include "abv1z.mm"
include "mpan2.mm"
include "adantr.mm"
include "cc.mm"
include "qcn.mm"
include "adantl.mm"
include "exp0d.mm"
include "qrngbas.mm"
include "abvcl.mm"
include "recnd.mm"
include "3eqtr4d.mm"
include "cmul.mm"
include "oveq1.mm"
include "expp1.mm"
include "sylan.mm"
include "simpll.mm"
include "qexpcl.mm"
include "adantll.mm"
include "simplr.mm"
include "cvv.mm"
include "cmulr.mm"
include "qex.mm"
include "ccnfld.mm"
include "cnfldmul.mm"
include "ressmulr.mm"
include "ax-mp.mm"
include "abvmul.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "com12.mm"
include "3impia.mm"

theorem qabvexp
  let cA: class A
  let cQ: class Q
  let cF: class F
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cK: class K
  let vj: setvar j
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let vq: setvar q
  let wph: wff ph
  let vg: setvar g
  let cJ: class J
  let cS: class S
  let cT: class T
  let cU: class U
  let cX: class X
  let cY: class Y
  let cP: class P
  let cR: class R
  assume qrng.q: |- Q = ( CCfld |`s QQ )
  assume qabsabv.a: |- A = ( AbsVal ` Q )


  assert |- ( ( F e. A /\ M e. QQ /\ N e. NN0 ) -> ( F ` ( M ^ N ) ) = ( ( F ` M ) ^ N ) )

  proof
    cF
    cA
    wcel
    #
    cM
    cq
    wcel
    #
    cN
    cn0
    wcel
    #
    cM
    cN
    cexp
    co
    #
    cF
    cfv
    #
    cM
    cF
    cfv
    #
    cN
    cexp
    co
    #
    wceq
    #
    @2
    @0
    @1
    wa
    #
    @7
    @8
    cM
    vk
    cv
    #
    cexp
    co
    #
    cF
    cfv
    #
    @5
    @9
    cexp
    co
    #
    wceq
    #
    wi
    @8
    cM
    cc0
    cexp
    co
    #
    cF
    cfv
    #
    @5
    cc0
    cexp
    co
    #
    wceq
    #
    wi
    @8
    cM
    vn
    cv
    #
    cexp
    co
    #
    cF
    cfv
    #
    @5
    @18
    cexp
    co
    #
    wceq
    #
    wi
    @8
    cM
    @18
    c1
    caddc
    co
    #
    cexp
    co
    #
    cF
    cfv
    #
    @5
    @23
    cexp
    co
    #
    wceq
    #
    wi
    @8
    @7
    wi
    vk
    vn
    cN
    @9
    cc0
    wceq
    #
    @13
    @17
    @8
    @28
    @11
    @15
    @12
    @16
    @28
    @10
    @14
    cF
    @9
    cc0
    cM
    cexp
    oveq2
    fveq2d
    @9
    cc0
    @5
    cexp
    oveq2
    eqeq12d
    imbi2d
    @9
    @18
    wceq
    #
    @13
    @22
    @8
    @29
    @11
    @20
    @12
    @21
    @29
    @10
    @19
    cF
    @9
    @18
    cM
    cexp
    oveq2
    fveq2d
    @9
    @18
    @5
    cexp
    oveq2
    eqeq12d
    imbi2d
    @9
    @23
    wceq
    #
    @13
    @27
    @8
    @30
    @11
    @25
    @12
    @26
    @30
    @10
    @24
    cF
    @9
    @23
    cM
    cexp
    oveq2
    fveq2d
    @9
    @23
    @5
    cexp
    oveq2
    eqeq12d
    imbi2d
    @9
    cN
    wceq
    #
    @13
    @7
    @8
    @31
    @11
    @4
    @12
    @6
    @31
    @10
    @3
    cF
    @9
    cN
    cM
    cexp
    oveq2
    fveq2d
    @9
    cN
    @5
    cexp
    oveq2
    eqeq12d
    imbi2d
    @8
    c1
    cF
    cfv
    #
    c1
    @15
    @16
    @0
    @32
    c1
    wceq
    #
    @1
    @0
    c1
    cc0
    wne
    @33
    ax-1ne0
    cA
    cQ
    c1
    cF
    cc0
    qabsabv.a
    cQ
    qrng.q
    qrng1
    cQ
    qrng.q
    qrng0
    abv1z
    mpan2
    adantr
    @8
    @14
    c1
    cF
    @8
    cM
    @1
    cM
    cc
    wcel
    #
    @0
    cM
    qcn
    adantl
    #
    exp0d
    fveq2d
    @8
    @5
    @8
    @5
    cA
    cq
    cQ
    cF
    cM
    qabsabv.a
    cQ
    qrng.q
    qrngbas
    #
    abvcl
    recnd
    #
    exp0d
    3eqtr4d
    @18
    cn0
    wcel
    #
    @8
    @22
    @27
    @8
    @38
    @22
    @27
    wi
    @22
    @27
    @8
    @38
    wa
    #
    @20
    @5
    cmul
    co
    #
    @21
    @5
    cmul
    co
    #
    wceq
    @20
    @21
    @5
    cmul
    oveq1
    @39
    @25
    @40
    @26
    @41
    @39
    @25
    @19
    cM
    cmul
    co
    #
    cF
    cfv
    #
    @40
    @39
    @24
    @42
    cF
    @8
    @34
    @38
    @24
    @42
    wceq
    @35
    cM
    @18
    expp1
    sylan
    fveq2d
    @39
    @0
    @19
    cq
    wcel
    #
    @1
    @43
    @40
    wceq
    @0
    @1
    @38
    simpll
    @1
    @38
    @44
    @0
    cM
    @18
    qexpcl
    adantll
    @0
    @1
    @38
    simplr
    cA
    cq
    cQ
    cmul
    cF
    @19
    cM
    qabsabv.a
    @36
    cq
    cvv
    wcel
    cmul
    cQ
    cmulr
    cfv
    wceq
    qex
    cq
    ccnfld
    cQ
    cmul
    cvv
    qrng.q
    cnfldmul
    ressmulr
    ax-mp
    abvmul
    syl3anc
    eqtrd
    @8
    @5
    cc
    wcel
    @38
    @26
    @41
    wceq
    @37
    @5
    @18
    expp1
    sylan
    eqeq12d
    syl5ibr
    expcom
    a2d
    nn0ind
    com12
    3impia
end
