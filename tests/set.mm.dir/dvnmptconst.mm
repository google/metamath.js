include "cn.mm"
include "wcel.mm"
include "cmpt.mm"
include "cdvn.mm"
include "co.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "id.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "cdv.mm"
include "cc.mm"
include "wss.mm"
include "cpm.mm"
include "cr.mm"
include "cpr.mm"
include "recnprss.mm"
include "syl.mm"
include "cvv.mm"
include "adantr.mm"
include "cpw.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "restsspw.mm"
include "sseldi.mm"
include "elpwi.mm"
include "cnex.mm"
include "a1i.mm"
include "mptelpm.mm"
include "dvn1.mm"
include "syl2anc.mm"
include "dvmptconst.mm"
include "eqtrd.mm"
include "w3a.mm"
include "simp3.mm"
include "simp1.mm"
include "wa.mm"
include "simpr.mm"
include "simpl.mm"
include "pm3.35.mm"
include "3adant1.mm"
include "cn0.mm"
include "3ad2ant1.mm"
include "nnnn0.mm"
include "3ad2ant2.mm"
include "dvnp1.mm"
include "syl3anc.mm"
include "oveq2.mm"
include "3ad2ant3.mm"
include "0cnd.mm"
include "3eqtrd.mm"
include "3exp.mm"
include "nnind.mm"
include "sylc.mm"

theorem dvnmptconst
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cN: class N
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vk: setvar k
  assume dvnmptconst.s: |- ( ph -> S e. { RR , CC } )
  assume dvnmptconst.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume dvnmptconst.a: |- ( ph -> A e. CC )
  assume dvnmptconst.n: |- ( ph -> N e. NN )

  disjoint A x
  disjoint S x
  disjoint X x
  disjoint ph x
  disjoint A m
  disjoint A n
  disjoint m n
  disjoint m x
  disjoint n x
  disjoint N n
  disjoint S m
  disjoint S n
  disjoint X m
  disjoint X n
  disjoint m ph
  disjoint n ph
  disjoint k x
  assert |- ( ph -> ( ( S Dn ( x e. X |-> A ) ) ` N ) = ( x e. X |-> 0 ) )

  proof
    wph
    cN
    cn
    wcel
    wph
    cN
    cS
    vx
    cX
    cA
    cmpt
    #
    cdvn
    co
    #
    cfv
    #
    vx
    cX
    cc0
    cmpt
    #
    wceq
    #
    dvnmptconst.n
    wph
    id
    wph
    vn
    cv
    #
    @1
    cfv
    #
    @3
    wceq
    #
    wi
    wph
    c1
    @1
    cfv
    #
    @3
    wceq
    #
    wi
    wph
    vm
    cv
    #
    @1
    cfv
    #
    @3
    wceq
    #
    wi
    #
    wph
    @10
    c1
    caddc
    co
    #
    @1
    cfv
    #
    @3
    wceq
    #
    wi
    wph
    @4
    wi
    vn
    vm
    cN
    @5
    c1
    wceq
    #
    @7
    @9
    wph
    @17
    @6
    @8
    @3
    @5
    c1
    @1
    fveq2
    eqeq1d
    imbi2d
    @5
    @10
    wceq
    #
    @7
    @12
    wph
    @18
    @6
    @11
    @3
    @5
    @10
    @1
    fveq2
    eqeq1d
    imbi2d
    @5
    @14
    wceq
    #
    @7
    @16
    wph
    @19
    @6
    @15
    @3
    @5
    @14
    @1
    fveq2
    eqeq1d
    imbi2d
    @5
    cN
    wceq
    #
    @7
    @4
    wph
    @20
    @6
    @2
    @3
    @5
    cN
    @1
    fveq2
    eqeq1d
    imbi2d
    wph
    @8
    cS
    @0
    cdv
    co
    #
    @3
    wph
    cS
    cc
    wss
    #
    @0
    cc
    cS
    cpm
    co
    wcel
    #
    @8
    @21
    wceq
    wph
    cS
    cr
    cc
    cpr
    #
    wcel
    @22
    dvnmptconst.s
    cS
    recnprss
    syl
    #
    wph
    vx
    cX
    cA
    cc
    cS
    cvv
    @24
    wph
    cA
    cc
    wcel
    vx
    cv
    cX
    wcel
    dvnmptconst.a
    adantr
    wph
    cX
    cS
    cpw
    #
    wcel
    cX
    cS
    wss
    wph
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    @26
    cX
    cS
    @27
    restsspw
    dvnmptconst.x
    sseldi
    cX
    cS
    elpwi
    syl
    cc
    cvv
    wcel
    wph
    cnex
    a1i
    dvnmptconst.s
    mptelpm
    #
    cS
    @0
    dvn1
    syl2anc
    wph
    vx
    cX
    cA
    cS
    dvnmptconst.s
    dvnmptconst.x
    dvnmptconst.a
    dvmptconst
    eqtrd
    @10
    cn
    wcel
    #
    @13
    wph
    @16
    @29
    @13
    wph
    w3a
    wph
    @29
    @12
    @16
    @29
    @13
    wph
    simp3
    @29
    @13
    wph
    simp1
    @13
    wph
    @12
    @29
    @13
    wph
    wa
    wph
    @13
    @12
    @13
    wph
    simpr
    @13
    wph
    simpl
    wph
    @12
    pm3.35
    syl2anc
    3adant1
    wph
    @29
    @12
    w3a
    #
    @15
    cS
    @11
    cdv
    co
    #
    cS
    @3
    cdv
    co
    #
    @3
    @30
    @22
    @23
    @10
    cn0
    wcel
    #
    @15
    @31
    wceq
    wph
    @29
    @22
    @12
    @25
    3ad2ant1
    wph
    @29
    @23
    @12
    @28
    3ad2ant1
    @29
    wph
    @33
    @12
    @10
    nnnn0
    3ad2ant2
    cS
    @0
    @10
    dvnp1
    syl3anc
    @12
    wph
    @31
    @32
    wceq
    @29
    @11
    @3
    cS
    cdv
    oveq2
    3ad2ant3
    wph
    @29
    @32
    @3
    wceq
    @12
    wph
    vx
    cX
    cc0
    cS
    dvnmptconst.s
    dvnmptconst.x
    wph
    0cnd
    dvmptconst
    3ad2ant1
    3eqtrd
    syl3anc
    3exp
    nnind
    sylc
end
