include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "wne.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "simprl.mm"
include "eqid.mm"
include "dmatmat.mm"
include "com12.mm"
include "adantl.mm"
include "impcom.mm"
include "jca.mm"
include "matvscl.mm"
include "syldan.mm"
include "wb.mm"
include "dmatel.mm"
include "adantr.mm"
include "cmulr.mm"
include "w3a.mm"
include "simp-4r.mm"
include "simpr.mm"
include "anim1i.mm"
include "3jca.mm"
include "matvscacell.mm"
include "syl.mm"
include "oveq2.mm"
include "ringrz.mm"
include "3eqtrd.mm"
include "ex.mm"
include "imim2d.mm"
include "ralimdvva.mm"
include "expimpd.mm"
include "sylbid.mm"
include "impr.mm"
include "mpbir2and.mm"

theorem dmatscmcl
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let c.as: class .*
  let cK: class K
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  assume dmatscmcl.k: |- K = ( Base ` R )
  assume dmatscmcl.a: |- A = ( N Mat R )
  assume dmatscmcl.b: |- B = ( Base ` A )
  assume dmatscmcl.s: |- .* = ( .s ` A )
  assume dmatscmcl.d: |- D = ( N DMat R )


  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ ( C e. K /\ M e. D ) ) -> ( C .* M ) e. D )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cC
    cK
    wcel
    #
    cM
    cD
    wcel
    #
    wa
    #
    wa
    #
    cC
    cM
    c.as
    co
    #
    cD
    wcel
    #
    @7
    cB
    wcel
    #
    vi
    cv
    #
    vj
    cv
    #
    wne
    #
    @10
    @11
    @7
    co
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    @2
    @5
    @3
    cM
    cB
    wcel
    #
    wa
    #
    @9
    @6
    @3
    @18
    @2
    @3
    @4
    simprl
    @5
    @2
    @18
    @4
    @2
    @18
    wi
    @3
    @2
    @4
    @18
    cA
    cB
    cD
    cR
    cM
    cN
    crg
    @14
    dmatscmcl.a
    dmatscmcl.b
    @14
    eqid
    #
    dmatscmcl.d
    dmatmat
    com12
    adantl
    impcom
    jca
    cA
    cB
    cC
    cR
    c.as
    cK
    cN
    cM
    dmatscmcl.k
    dmatscmcl.a
    dmatscmcl.b
    dmatscmcl.s
    matvscl
    syldan
    @2
    @3
    @4
    @17
    @2
    @3
    wa
    #
    @4
    @18
    @12
    @10
    @11
    cM
    co
    #
    @14
    wceq
    #
    wi
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    wa
    #
    @17
    @2
    @4
    @26
    wb
    @3
    cA
    cB
    cD
    cR
    vi
    vj
    cM
    cN
    crg
    @14
    dmatscmcl.a
    dmatscmcl.b
    @20
    dmatscmcl.d
    dmatel
    adantr
    @21
    @18
    @25
    @17
    @21
    @18
    wa
    #
    @24
    @16
    vi
    vj
    cN
    cN
    @27
    @10
    cN
    wcel
    @11
    cN
    wcel
    wa
    #
    wa
    #
    @23
    @15
    @12
    @29
    @23
    @15
    @29
    @23
    wa
    #
    @13
    cC
    @22
    cR
    cmulr
    cfv
    #
    co
    #
    cC
    @14
    @31
    co
    #
    @14
    @30
    @1
    @19
    @28
    w3a
    #
    @13
    @32
    wceq
    @29
    @34
    @23
    @29
    @1
    @19
    @28
    @0
    @1
    @3
    @18
    @28
    simp-4r
    @27
    @19
    @28
    @21
    @3
    @18
    @2
    @3
    simpr
    anim1i
    adantr
    @27
    @28
    simpr
    3jca
    adantr
    cA
    cB
    cR
    c.as
    @31
    @10
    @11
    cK
    cN
    cC
    cM
    dmatscmcl.a
    dmatscmcl.b
    dmatscmcl.k
    dmatscmcl.s
    @31
    eqid
    #
    matvscacell
    syl
    @23
    @32
    @33
    wceq
    @29
    @22
    @14
    cC
    @31
    oveq2
    adantl
    @29
    @33
    @14
    wceq
    #
    @23
    @27
    @36
    @28
    @27
    @1
    @3
    wa
    #
    @36
    @21
    @37
    @18
    @2
    @1
    @3
    @0
    @1
    simpr
    anim1i
    adantr
    cK
    cR
    @31
    cC
    @14
    dmatscmcl.k
    @35
    @20
    ringrz
    syl
    adantr
    adantr
    3eqtrd
    ex
    imim2d
    ralimdvva
    expimpd
    sylbid
    impr
    @2
    @8
    @9
    @17
    wa
    wb
    @5
    cA
    cB
    cD
    cR
    vi
    vj
    @7
    cN
    crg
    @14
    dmatscmcl.a
    dmatscmcl.b
    @20
    dmatscmcl.d
    dmatel
    adantr
    mpbir2and
end
