include "cn0.mm"
include "wcel.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "fveq2.mm"
include "id.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "qrng0.mm"
include "abv0.mm"
include "0le0.mm"
include "syl6eqbr.mm"
include "wa.mm"
include "cq.mm"
include "cr.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "ad2antrl.mm"
include "nnq.mm"
include "syl.mm"
include "qrngbas.mm"
include "abvcl.mm"
include "syldan.mm"
include "cz.mm"
include "nn0z.mm"
include "zq.mm"
include "peano2re.mm"
include "zred.mm"
include "simpl.mm"
include "1z.mm"
include "mp1i.mm"
include "cvv.mm"
include "cplusg.mm"
include "qex.mm"
include "ccnfld.mm"
include "cnfldadd.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "abvtri.mm"
include "syl3anc.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "qrng1.mm"
include "abv1z.mm"
include "mpan2.mm"
include "adantr.mm"
include "oveq2d.mm"
include "breqtrd.mm"
include "1red.mm"
include "simprr.mm"
include "leadd1dd.mm"
include "letrd.mm"
include "expr.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"

theorem qabvle
  let cA: class A
  let cQ: class Q
  let cF: class F
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
  let cM: class M
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


  assert |- ( ( F e. A /\ N e. NN0 ) -> ( F ` N ) <_ N )

  proof
    cN
    cn0
    wcel
    cF
    cA
    wcel
    #
    cN
    cF
    cfv
    #
    cN
    cle
    wbr
    #
    @0
    vk
    cv
    #
    cF
    cfv
    #
    @3
    cle
    wbr
    #
    wi
    @0
    cc0
    cF
    cfv
    #
    cc0
    cle
    wbr
    #
    wi
    @0
    vn
    cv
    #
    cF
    cfv
    #
    @8
    cle
    wbr
    #
    wi
    @0
    @8
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @11
    cle
    wbr
    #
    wi
    @0
    @2
    wi
    vk
    vn
    cN
    @3
    cc0
    wceq
    #
    @5
    @7
    @0
    @14
    @4
    @6
    @3
    cc0
    cle
    @3
    cc0
    cF
    fveq2
    @14
    id
    breq12d
    imbi2d
    @3
    @8
    wceq
    #
    @5
    @10
    @0
    @15
    @4
    @9
    @3
    @8
    cle
    @3
    @8
    cF
    fveq2
    @15
    id
    breq12d
    imbi2d
    @3
    @11
    wceq
    #
    @5
    @13
    @0
    @16
    @4
    @12
    @3
    @11
    cle
    @3
    @11
    cF
    fveq2
    @16
    id
    breq12d
    imbi2d
    @3
    cN
    wceq
    #
    @5
    @2
    @0
    @17
    @4
    @1
    @3
    cN
    cle
    @3
    cN
    cF
    fveq2
    @17
    id
    breq12d
    imbi2d
    @0
    @6
    cc0
    cc0
    cle
    cA
    cQ
    cF
    cc0
    qabsabv.a
    cQ
    qrng.q
    qrng0
    #
    abv0
    0le0
    syl6eqbr
    @8
    cn0
    wcel
    #
    @0
    @10
    @13
    @0
    @19
    @10
    @13
    wi
    @0
    @19
    @10
    @13
    @0
    @19
    @10
    wa
    #
    wa
    #
    @12
    @9
    c1
    caddc
    co
    #
    @11
    @0
    @20
    @11
    cq
    wcel
    #
    @12
    cr
    wcel
    @21
    @11
    cn
    wcel
    #
    @23
    @19
    @24
    @0
    @10
    @8
    nn0p1nn
    ad2antrl
    @11
    nnq
    syl
    cA
    cq
    cQ
    cF
    @11
    qabsabv.a
    cQ
    qrng.q
    qrngbas
    #
    abvcl
    syldan
    @21
    @9
    cr
    wcel
    #
    @22
    cr
    wcel
    @0
    @20
    @8
    cq
    wcel
    #
    @26
    @21
    @8
    cz
    wcel
    #
    @27
    @19
    @28
    @0
    @10
    @8
    nn0z
    ad2antrl
    #
    @8
    zq
    syl
    #
    cA
    cq
    cQ
    cF
    @8
    qabsabv.a
    @25
    abvcl
    syldan
    #
    @9
    peano2re
    syl
    @21
    @8
    cr
    wcel
    @11
    cr
    wcel
    @21
    @8
    @29
    zred
    #
    @8
    peano2re
    syl
    @21
    @12
    @9
    c1
    cF
    cfv
    #
    caddc
    co
    #
    @22
    cle
    @21
    @0
    @27
    c1
    cq
    wcel
    #
    @12
    @34
    cle
    wbr
    @0
    @20
    simpl
    @30
    c1
    cz
    wcel
    @35
    @21
    1z
    c1
    zq
    mp1i
    cA
    cq
    caddc
    cQ
    cF
    @8
    c1
    qabsabv.a
    @25
    cq
    cvv
    wcel
    caddc
    cQ
    cplusg
    cfv
    wceq
    qex
    cq
    caddc
    ccnfld
    cQ
    cvv
    qrng.q
    cnfldadd
    ressplusg
    ax-mp
    abvtri
    syl3anc
    @21
    @33
    c1
    @9
    caddc
    @0
    @33
    c1
    wceq
    #
    @20
    @0
    c1
    cc0
    wne
    @36
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
    @18
    abv1z
    mpan2
    adantr
    oveq2d
    breqtrd
    @21
    @9
    @8
    c1
    @31
    @32
    @21
    1red
    @0
    @19
    @10
    simprr
    leadd1dd
    letrd
    expr
    expcom
    a2d
    nn0ind
    impcom
end
