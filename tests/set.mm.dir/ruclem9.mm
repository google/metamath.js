include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1st.mm"
include "cle.mm"
include "wbr.mm"
include "c2nd.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "imbi2d.mm"
include "cz.mm"
include "cr.mm"
include "cxp.mm"
include "cn0.mm"
include "ruclem6.mm"
include "ffvelrnd.mm"
include "xp1st.mm"
include "syl.mm"
include "leidd.mm"
include "xp2nd.mm"
include "jca.mm"
include "a1i.mm"
include "cop.mm"
include "clt.mm"
include "cn.mm"
include "wf.mm"
include "adantr.mm"
include "c2.mm"
include "cdiv.mm"
include "cif.mm"
include "csb.mm"
include "cmpt2.mm"
include "eluznn0.mm"
include "sylan.mm"
include "nn0p1nn.mm"
include "eqid.mm"
include "ruclem8.mm"
include "syldan.mm"
include "ruclem2.mm"
include "simp1d.mm"
include "ruclem7.mm"
include "1st2nd2.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "peano2nn0.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "simp3d.mm"
include "eqbrtrd.mm"
include "mpand.mm"
include "anim12d.mm"
include "expcom.mm"
include "a2d.mm"
include "uzind4.mm"
include "mpcom.mm"

theorem ruclem9
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vw: setvar w
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vn: setvar n
  let vk: setvar k
  let cS: class S
  assume ruc.1: |- ( ph -> F : NN --> RR )
  assume ruc.2: |- ( ph -> D = ( x e. ( RR X. RR ) , y e. RR |-> [_ ( ( ( 1st ` x ) + ( 2nd ` x ) ) / 2 ) / m ]_ if ( m < y , <. ( 1st ` x ) , m >. , <. ( ( m + ( 2nd ` x ) ) / 2 ) , ( 2nd ` x ) >. ) ) )
  assume ruc.4: |- C = ( { <. 0 , <. 0 , 1 >. >. } u. F )
  assume ruc.5: |- G = seq 0 ( D , C )
  assume ruclem9.6: |- ( ph -> M e. NN0 )
  assume ruclem9.7: |- ( ph -> N e. ( ZZ>= ` M ) )

  disjoint m x
  disjoint m y
  disjoint x y
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint G m
  disjoint G x
  disjoint G y
  disjoint M m
  disjoint M x
  disjoint M y
  disjoint N m
  disjoint N x
  disjoint N y
  disjoint m w
  disjoint w x
  disjoint w y
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint w z
  disjoint C w
  disjoint C z
  disjoint m n
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint G k
  disjoint G n
  disjoint G z
  disjoint M k
  disjoint M n
  disjoint N k
  disjoint k w
  disjoint k ph
  disjoint n w
  disjoint n ph
  disjoint ph w
  disjoint ph z
  disjoint D w
  disjoint D z
  disjoint S n
  disjoint S z
  assert |- ( ph -> ( ( 1st ` ( G ` M ) ) <_ ( 1st ` ( G ` N ) ) /\ ( 2nd ` ( G ` N ) ) <_ ( 2nd ` ( G ` M ) ) ) )

  proof
    cN
    cM
    cuz
    cfv
    #
    wcel
    wph
    cM
    cG
    cfv
    #
    c1st
    cfv
    #
    cN
    cG
    cfv
    #
    c1st
    cfv
    #
    cle
    wbr
    #
    @3
    c2nd
    cfv
    #
    @1
    c2nd
    cfv
    #
    cle
    wbr
    #
    wa
    #
    ruclem9.7
    wph
    @2
    vk
    cv
    #
    cG
    cfv
    #
    c1st
    cfv
    #
    cle
    wbr
    #
    @11
    c2nd
    cfv
    #
    @7
    cle
    wbr
    #
    wa
    #
    wi
    wph
    @2
    @2
    cle
    wbr
    #
    @7
    @7
    cle
    wbr
    #
    wa
    #
    wi
    #
    wph
    @2
    vn
    cv
    #
    cG
    cfv
    #
    c1st
    cfv
    #
    cle
    wbr
    #
    @22
    c2nd
    cfv
    #
    @7
    cle
    wbr
    #
    wa
    #
    wi
    wph
    @2
    @21
    c1
    caddc
    co
    #
    cG
    cfv
    #
    c1st
    cfv
    #
    cle
    wbr
    #
    @29
    c2nd
    cfv
    #
    @7
    cle
    wbr
    #
    wa
    #
    wi
    wph
    @9
    wi
    vk
    vn
    cM
    cN
    @10
    cM
    wceq
    #
    @16
    @19
    wph
    @35
    @13
    @17
    @15
    @18
    @35
    @12
    @2
    @2
    cle
    @35
    @11
    @1
    c1st
    @10
    cM
    cG
    fveq2
    #
    fveq2d
    breq2d
    @35
    @14
    @7
    @7
    cle
    @35
    @11
    @1
    c2nd
    @36
    fveq2d
    breq1d
    anbi12d
    imbi2d
    @10
    @21
    wceq
    #
    @16
    @27
    wph
    @37
    @13
    @24
    @15
    @26
    @37
    @12
    @23
    @2
    cle
    @37
    @11
    @22
    c1st
    @10
    @21
    cG
    fveq2
    #
    fveq2d
    breq2d
    @37
    @14
    @25
    @7
    cle
    @37
    @11
    @22
    c2nd
    @38
    fveq2d
    breq1d
    anbi12d
    imbi2d
    @10
    @28
    wceq
    #
    @16
    @34
    wph
    @39
    @13
    @31
    @15
    @33
    @39
    @12
    @30
    @2
    cle
    @39
    @11
    @29
    c1st
    @10
    @28
    cG
    fveq2
    #
    fveq2d
    breq2d
    @39
    @14
    @32
    @7
    cle
    @39
    @11
    @29
    c2nd
    @40
    fveq2d
    breq1d
    anbi12d
    imbi2d
    @10
    cN
    wceq
    #
    @16
    @9
    wph
    @41
    @13
    @5
    @15
    @8
    @41
    @12
    @4
    @2
    cle
    @41
    @11
    @3
    c1st
    @10
    cN
    cG
    fveq2
    #
    fveq2d
    breq2d
    @41
    @14
    @6
    @7
    cle
    @41
    @11
    @3
    c2nd
    @42
    fveq2d
    breq1d
    anbi12d
    imbi2d
    @20
    cM
    cz
    wcel
    wph
    @17
    @18
    wph
    @2
    wph
    @1
    cr
    cr
    cxp
    #
    wcel
    #
    @2
    cr
    wcel
    #
    wph
    cn0
    @43
    cM
    cG
    wph
    vx
    vy
    cC
    cD
    vm
    cF
    cG
    ruc.1
    ruc.2
    ruc.4
    ruc.5
    ruclem6
    #
    ruclem9.6
    ffvelrnd
    #
    @1
    cr
    cr
    xp1st
    syl
    #
    leidd
    wph
    @7
    wph
    @44
    @7
    cr
    wcel
    #
    @47
    @1
    cr
    cr
    xp2nd
    syl
    #
    leidd
    jca
    a1i
    @21
    @0
    wcel
    #
    wph
    @27
    @34
    wph
    @51
    @27
    @34
    wi
    wph
    @51
    wa
    #
    @24
    @31
    @26
    @33
    @52
    @24
    @23
    @30
    cle
    wbr
    #
    @31
    @52
    @23
    @23
    @25
    cop
    #
    @28
    cF
    cfv
    #
    cD
    co
    #
    c1st
    cfv
    #
    @30
    cle
    @52
    @23
    @57
    cle
    wbr
    #
    @57
    @56
    c2nd
    cfv
    #
    clt
    wbr
    #
    @59
    @25
    cle
    wbr
    #
    @52
    vx
    vy
    @23
    @25
    cD
    vm
    cF
    @55
    @57
    @59
    wph
    cn
    cr
    cF
    wf
    @51
    ruc.1
    adantr
    #
    wph
    cD
    vx
    vy
    @43
    cr
    vm
    vx
    cv
    #
    c1st
    cfv
    #
    @63
    c2nd
    cfv
    #
    caddc
    co
    c2
    cdiv
    co
    vm
    cv
    #
    vy
    cv
    clt
    wbr
    @64
    @66
    cop
    @66
    @65
    caddc
    co
    c2
    cdiv
    co
    @65
    cop
    cif
    csb
    cmpt2
    wceq
    @51
    ruc.2
    adantr
    @52
    @22
    @43
    wcel
    #
    @23
    cr
    wcel
    #
    @52
    cn0
    @43
    @21
    cG
    wph
    cn0
    @43
    cG
    wf
    @51
    @46
    adantr
    #
    wph
    cM
    cn0
    wcel
    @51
    @21
    cn0
    wcel
    #
    ruclem9.6
    @21
    cM
    eluznn0
    sylan
    #
    ffvelrnd
    #
    @22
    cr
    cr
    xp1st
    syl
    #
    @52
    @67
    @25
    cr
    wcel
    #
    @72
    @22
    cr
    cr
    xp2nd
    syl
    #
    @52
    cn
    cr
    @28
    cF
    @62
    @52
    @70
    @28
    cn
    wcel
    @71
    @21
    nn0p1nn
    syl
    ffvelrnd
    @57
    eqid
    @59
    eqid
    wph
    @51
    @70
    @23
    @25
    clt
    wbr
    @71
    wph
    vx
    vy
    cC
    cD
    vm
    cF
    cG
    @21
    ruc.1
    ruc.2
    ruc.4
    ruc.5
    ruclem8
    syldan
    ruclem2
    #
    simp1d
    @52
    @29
    @56
    c1st
    @52
    @29
    @22
    @55
    cD
    co
    #
    @56
    wph
    @51
    @70
    @29
    @77
    wceq
    @71
    wph
    vx
    vy
    cC
    cD
    vm
    cF
    cG
    @21
    ruc.1
    ruc.2
    ruc.4
    ruc.5
    ruclem7
    syldan
    @52
    @22
    @54
    @55
    cD
    @52
    @67
    @22
    @54
    wceq
    @72
    @22
    cr
    cr
    1st2nd2
    syl
    oveq1d
    eqtrd
    #
    fveq2d
    breqtrrd
    @52
    @45
    @68
    @30
    cr
    wcel
    #
    @24
    @53
    wa
    @31
    wi
    wph
    @45
    @51
    @48
    adantr
    @73
    @52
    @29
    @43
    wcel
    #
    @79
    @52
    cn0
    @43
    @28
    cG
    @69
    @52
    @70
    @28
    cn0
    wcel
    @71
    @21
    peano2nn0
    syl
    ffvelrnd
    #
    @29
    cr
    cr
    xp1st
    syl
    @2
    @23
    @30
    letr
    syl3anc
    mpan2d
    @52
    @32
    @25
    cle
    wbr
    #
    @26
    @33
    @52
    @32
    @59
    @25
    cle
    @52
    @29
    @56
    c2nd
    @78
    fveq2d
    @52
    @58
    @60
    @61
    @76
    simp3d
    eqbrtrd
    @52
    @32
    cr
    wcel
    #
    @74
    @49
    @82
    @26
    wa
    @33
    wi
    @52
    @80
    @83
    @81
    @29
    cr
    cr
    xp2nd
    syl
    @75
    wph
    @49
    @51
    @50
    adantr
    @32
    @25
    @7
    letr
    syl3anc
    mpand
    anim12d
    expcom
    a2d
    uzind4
    mpcom
end
