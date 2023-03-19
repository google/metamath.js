include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "c2nd.mm"
include "cfv.mm"
include "cc0.mm"
include "c1st.mm"
include "chash.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cfz.mm"
include "wral.mm"
include "wa.mm"
include "cfzo.mm"
include "cvtx.mm"
include "cword.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "clwlksf1clwwlklem3.mm"
include "anim12ci.mm"
include "adantr.mm"
include "nnnn0.mm"
include "adantl.mm"
include "clwlksf1clwwlklem1.mm"
include "3jca.mm"
include "jca.mm"
include "exp31.mm"
include "3imp31.mm"
include "clwlksfclwwlk1hashn.mm"
include "3ad2ant2.mm"
include "opeq2d.mm"
include "oveq2d.mm"
include "3ad2ant3.mm"
include "eqeq12d.mm"
include "biimpa.mm"
include "wb.mm"
include "simpl.mm"
include "id.mm"
include "3ad2ant1.mm"
include "3simpc.mm"
include "swrdeq.mm"
include "syl3anc.mm"
include "simpr.mm"
include "syl6bi.mm"
include "sylc.mm"
include "wi.mm"
include "lbfzo0.mm"
include "biimpri.mm"
include "fveq2.mm"
include "rspcv.mm"
include "syl.mm"
include "clwlksf1clwwlklem2.mm"
include "sylibd.mm"
include "jcai.mm"
include "csn.mm"
include "cun.mm"
include "cuz.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "fzisfzounsn.mm"
include "raleqdv.mm"
include "simpl1.mm"
include "ralunsn.mm"
include "bitrd.mm"
include "mpbird.mm"
include "ex.mm"

theorem clwlksf1clwwlklem
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
  let cG: class G
  let cN: class N
  let cW: class W
  let vc: setvar c
  let vi: setvar i
  let vx: setvar x
  let vf: setvar f
  let vw: setvar w
  assume clwlksfclwwlk.1: |- A = ( 1st ` c )
  assume clwlksfclwwlk.2: |- B = ( 2nd ` c )
  assume clwlksfclwwlk.c: |- C = { c e. ( ClWalks ` G ) | ( # ` A ) = N }
  assume clwlksfclwwlk.f: |- F = ( c e. C |-> ( B substr <. 0 , ( # ` A ) >. ) )

  disjoint G c
  disjoint N c
  disjoint W c
  disjoint C c
  disjoint F c
  disjoint G y
  disjoint N y
  disjoint U c
  disjoint U y
  disjoint c y
  disjoint W y
  disjoint A i
  disjoint B i
  disjoint G i
  disjoint c i
  disjoint C i
  disjoint G x
  disjoint i x
  disjoint N i
  disjoint C f
  disjoint C w
  disjoint f w
  disjoint F f
  disjoint F w
  disjoint c f
  disjoint c w
  disjoint G f
  disjoint G w
  disjoint N f
  disjoint N w
  disjoint W i
  assert |- ( ( N e. NN /\ U e. C /\ W e. C ) -> ( ( ( 2nd ` U ) substr <. 0 , ( # ` ( 1st ` U ) ) >. ) = ( ( 2nd ` W ) substr <. 0 , ( # ` ( 1st ` W ) ) >. ) -> A. y e. ( 0 ... N ) ( ( 2nd ` U ) ` y ) = ( ( 2nd ` W ) ` y ) ) )

  proof
    cN
    cn
    wcel
    #
    cU
    cC
    wcel
    #
    cW
    cC
    wcel
    #
    w3a
    #
    cU
    c2nd
    cfv
    #
    cc0
    cU
    c1st
    cfv
    chash
    cfv
    #
    cop
    #
    csubstr
    co
    #
    cW
    c2nd
    cfv
    #
    cc0
    cW
    c1st
    cfv
    chash
    cfv
    #
    cop
    #
    csubstr
    co
    #
    wceq
    #
    vy
    cv
    #
    @4
    cfv
    #
    @13
    @8
    cfv
    #
    wceq
    #
    vy
    cc0
    cN
    cfz
    co
    #
    wral
    #
    @3
    @12
    wa
    #
    @18
    @16
    vy
    cc0
    cN
    cfzo
    co
    #
    wral
    #
    cN
    @4
    cfv
    #
    cN
    @8
    cfv
    #
    wceq
    #
    wa
    #
    @19
    @21
    @24
    @19
    @4
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    @8
    @27
    wcel
    #
    wa
    #
    cN
    cn0
    wcel
    #
    cN
    @4
    chash
    cfv
    cle
    wbr
    #
    cN
    @8
    chash
    cfv
    cle
    wbr
    #
    w3a
    #
    wa
    #
    @4
    cc0
    cN
    cop
    #
    csubstr
    co
    #
    @8
    @36
    csubstr
    co
    #
    wceq
    #
    @21
    @3
    @35
    @12
    @2
    @1
    @0
    @35
    @2
    @1
    @0
    @35
    @2
    @1
    wa
    #
    @0
    wa
    #
    @30
    @34
    @40
    @30
    @0
    @2
    @29
    @1
    @28
    cA
    cB
    cC
    cF
    cG
    cN
    cW
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksf1clwwlklem3
    cA
    cB
    cC
    cF
    cG
    cN
    cU
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksf1clwwlklem3
    anim12ci
    adantr
    @41
    @31
    @32
    @33
    @0
    @31
    @40
    cN
    nnnn0
    #
    adantl
    @40
    @32
    @0
    @1
    @32
    @2
    cA
    cB
    cC
    cF
    cG
    cN
    cU
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksf1clwwlklem1
    adantl
    adantr
    @40
    @33
    @0
    @2
    @33
    @1
    cA
    cB
    cC
    cF
    cG
    cN
    cW
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksf1clwwlklem1
    adantr
    adantr
    3jca
    jca
    exp31
    3imp31
    adantr
    @3
    @12
    @39
    @3
    @7
    @37
    @11
    @38
    @3
    @6
    @36
    @4
    csubstr
    @3
    @5
    cN
    cc0
    @1
    @0
    @5
    cN
    wceq
    @2
    cA
    cB
    cC
    cF
    cG
    cN
    cU
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksfclwwlk1hashn
    3ad2ant2
    opeq2d
    oveq2d
    @3
    @10
    @36
    @8
    csubstr
    @3
    @9
    cN
    cc0
    @2
    @0
    @9
    cN
    wceq
    @1
    cA
    cB
    cC
    cF
    cG
    cN
    cW
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksfclwwlk1hashn
    3ad2ant3
    opeq2d
    oveq2d
    eqeq12d
    biimpa
    @35
    @39
    cN
    cN
    wceq
    #
    @21
    wa
    #
    @21
    @35
    @30
    @31
    @31
    wa
    #
    @32
    @33
    wa
    #
    @39
    @44
    wb
    @30
    @34
    simpl
    @34
    @45
    @30
    @31
    @32
    @45
    @33
    @31
    @31
    @31
    @31
    id
    #
    @47
    jca
    3ad2ant1
    adantl
    @34
    @46
    @30
    @31
    @32
    @33
    3simpc
    adantl
    @8
    vy
    cN
    cN
    @26
    @4
    swrdeq
    syl3anc
    @43
    @21
    simpr
    syl6bi
    sylc
    @19
    @21
    cc0
    @4
    cfv
    #
    cc0
    @8
    cfv
    #
    wceq
    #
    @24
    @19
    cc0
    @20
    wcel
    #
    @21
    @50
    wi
    @3
    @51
    @12
    @0
    @1
    @51
    @2
    @51
    @0
    cN
    lbfzo0
    biimpri
    3ad2ant1
    adantr
    @16
    @50
    vy
    cc0
    @20
    @13
    cc0
    wceq
    @14
    @48
    @15
    @49
    @13
    cc0
    @4
    fveq2
    @13
    cc0
    @8
    fveq2
    eqeq12d
    rspcv
    syl
    @19
    @48
    @22
    @49
    @23
    @3
    @48
    @22
    wceq
    #
    @12
    @1
    @0
    @52
    @2
    cA
    cB
    cC
    cF
    cG
    cN
    cU
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksf1clwwlklem2
    3ad2ant2
    adantr
    @3
    @49
    @23
    wceq
    #
    @12
    @2
    @0
    @53
    @1
    cA
    cB
    cC
    cF
    cG
    cN
    cW
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksf1clwwlklem2
    3ad2ant3
    adantr
    eqeq12d
    sylibd
    jcai
    @19
    @18
    @16
    vy
    @20
    cN
    csn
    cun
    #
    wral
    #
    @25
    @19
    @16
    vy
    @17
    @54
    @19
    cN
    cc0
    cuz
    cfv
    wcel
    #
    @17
    @54
    wceq
    @3
    @56
    @12
    @0
    @1
    @56
    @2
    @0
    @31
    @56
    @42
    cN
    elnn0uz
    sylib
    3ad2ant1
    adantr
    cc0
    cN
    fzisfzounsn
    syl
    raleqdv
    @19
    @0
    @55
    @25
    wb
    @0
    @1
    @2
    @12
    simpl1
    @16
    @24
    vy
    @20
    cN
    cn
    @13
    cN
    wceq
    @14
    @22
    @15
    @23
    @13
    cN
    @4
    fveq2
    @13
    cN
    @8
    fveq2
    eqeq12d
    ralunsn
    syl
    bitrd
    mpbird
    ex
end
