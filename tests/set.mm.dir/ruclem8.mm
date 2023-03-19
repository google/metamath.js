include "cn0.mm"
include "wcel.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "0lt1.mm"
include "a1i.mm"
include "cop.mm"
include "ruclem4.mm"
include "c0ex.mm"
include "1ex.mm"
include "op1st.mm"
include "syl6eq.mm"
include "op2nd.mm"
include "3brtr4d.mm"
include "wa.mm"
include "cle.mm"
include "cn.mm"
include "cr.mm"
include "wf.mm"
include "adantr.mm"
include "cxp.mm"
include "c2.mm"
include "cdiv.mm"
include "cif.mm"
include "csb.mm"
include "cmpt2.mm"
include "ruclem6.mm"
include "ffvelrnda.mm"
include "adantrr.mm"
include "xp1st.mm"
include "syl.mm"
include "xp2nd.mm"
include "nn0p1nn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "eqid.mm"
include "simprr.mm"
include "ruclem2.mm"
include "simp2d.mm"
include "ruclem7.mm"
include "1st2nd2.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "expr.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"

theorem ruclem8
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cN: class N
  let vw: setvar w
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vn: setvar n
  let vk: setvar k
  let cM: class M
  let cS: class S
  assume ruc.1: |- ( ph -> F : NN --> RR )
  assume ruc.2: |- ( ph -> D = ( x e. ( RR X. RR ) , y e. RR |-> [_ ( ( ( 1st ` x ) + ( 2nd ` x ) ) / 2 ) / m ]_ if ( m < y , <. ( 1st ` x ) , m >. , <. ( ( m + ( 2nd ` x ) ) / 2 ) , ( 2nd ` x ) >. ) ) )
  assume ruc.4: |- C = ( { <. 0 , <. 0 , 1 >. >. } u. F )
  assume ruc.5: |- G = seq 0 ( D , C )

  disjoint m x
  disjoint m y
  disjoint x y
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint G m
  disjoint G x
  disjoint G y
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
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M y
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
  assert |- ( ( ph /\ N e. NN0 ) -> ( 1st ` ( G ` N ) ) < ( 2nd ` ( G ` N ) ) )

  proof
    cN
    cn0
    wcel
    wph
    cN
    cG
    cfv
    #
    c1st
    cfv
    #
    @0
    c2nd
    cfv
    #
    clt
    wbr
    #
    wph
    vk
    cv
    #
    cG
    cfv
    #
    c1st
    cfv
    #
    @5
    c2nd
    cfv
    #
    clt
    wbr
    #
    wi
    wph
    cc0
    cG
    cfv
    #
    c1st
    cfv
    #
    @9
    c2nd
    cfv
    #
    clt
    wbr
    #
    wi
    wph
    vn
    cv
    #
    cG
    cfv
    #
    c1st
    cfv
    #
    @14
    c2nd
    cfv
    #
    clt
    wbr
    #
    wi
    wph
    @13
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
    @19
    c2nd
    cfv
    #
    clt
    wbr
    #
    wi
    wph
    @3
    wi
    vk
    vn
    cN
    @4
    cc0
    wceq
    #
    @8
    @12
    wph
    @23
    @6
    @10
    @7
    @11
    clt
    @23
    @5
    @9
    c1st
    @4
    cc0
    cG
    fveq2
    #
    fveq2d
    @23
    @5
    @9
    c2nd
    @24
    fveq2d
    breq12d
    imbi2d
    @4
    @13
    wceq
    #
    @8
    @17
    wph
    @25
    @6
    @15
    @7
    @16
    clt
    @25
    @5
    @14
    c1st
    @4
    @13
    cG
    fveq2
    #
    fveq2d
    @25
    @5
    @14
    c2nd
    @26
    fveq2d
    breq12d
    imbi2d
    @4
    @18
    wceq
    #
    @8
    @22
    wph
    @27
    @6
    @20
    @7
    @21
    clt
    @27
    @5
    @19
    c1st
    @4
    @18
    cG
    fveq2
    #
    fveq2d
    @27
    @5
    @19
    c2nd
    @28
    fveq2d
    breq12d
    imbi2d
    @4
    cN
    wceq
    #
    @8
    @3
    wph
    @29
    @6
    @1
    @7
    @2
    clt
    @29
    @5
    @0
    c1st
    @4
    cN
    cG
    fveq2
    #
    fveq2d
    @29
    @5
    @0
    c2nd
    @30
    fveq2d
    breq12d
    imbi2d
    wph
    cc0
    c1
    @10
    @11
    clt
    cc0
    c1
    clt
    wbr
    wph
    0lt1
    a1i
    wph
    @10
    cc0
    c1
    cop
    #
    c1st
    cfv
    cc0
    wph
    @9
    @31
    c1st
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
    ruclem4
    #
    fveq2d
    cc0
    c1
    c0ex
    1ex
    op1st
    syl6eq
    wph
    @11
    @31
    c2nd
    cfv
    c1
    wph
    @9
    @31
    c2nd
    @32
    fveq2d
    cc0
    c1
    c0ex
    1ex
    op2nd
    syl6eq
    3brtr4d
    @13
    cn0
    wcel
    #
    wph
    @17
    @22
    wph
    @33
    @17
    @22
    wi
    wph
    @33
    @17
    @22
    wph
    @33
    @17
    wa
    #
    wa
    #
    @15
    @16
    cop
    #
    @18
    cF
    cfv
    #
    cD
    co
    #
    c1st
    cfv
    #
    @38
    c2nd
    cfv
    #
    @20
    @21
    clt
    @35
    @15
    @39
    cle
    wbr
    @39
    @40
    clt
    wbr
    @40
    @16
    cle
    wbr
    @35
    vx
    vy
    @15
    @16
    cD
    vm
    cF
    @37
    @39
    @40
    wph
    cn
    cr
    cF
    wf
    #
    @34
    ruc.1
    adantr
    wph
    cD
    vx
    vy
    cr
    cr
    cxp
    #
    cr
    vm
    vx
    cv
    #
    c1st
    cfv
    #
    @43
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
    @44
    @46
    cop
    @46
    @45
    caddc
    co
    c2
    cdiv
    co
    @45
    cop
    cif
    csb
    cmpt2
    wceq
    @34
    ruc.2
    adantr
    @35
    @14
    @42
    wcel
    #
    @15
    cr
    wcel
    wph
    @33
    @47
    @17
    wph
    cn0
    @42
    @13
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
    ffvelrnda
    adantrr
    #
    @14
    cr
    cr
    xp1st
    syl
    @35
    @47
    @16
    cr
    wcel
    @48
    @14
    cr
    cr
    xp2nd
    syl
    wph
    @33
    @37
    cr
    wcel
    #
    @17
    wph
    @41
    @18
    cn
    wcel
    @49
    @33
    ruc.1
    @13
    nn0p1nn
    cn
    cr
    @18
    cF
    ffvelrn
    syl2an
    adantrr
    @39
    eqid
    @40
    eqid
    wph
    @33
    @17
    simprr
    ruclem2
    simp2d
    @35
    @19
    @38
    c1st
    @35
    @19
    @14
    @37
    cD
    co
    #
    @38
    wph
    @33
    @19
    @50
    wceq
    @17
    wph
    vx
    vy
    cC
    cD
    vm
    cF
    cG
    @13
    ruc.1
    ruc.2
    ruc.4
    ruc.5
    ruclem7
    adantrr
    @35
    @14
    @36
    @37
    cD
    @35
    @47
    @14
    @36
    wceq
    @48
    @14
    cr
    cr
    1st2nd2
    syl
    oveq1d
    eqtrd
    #
    fveq2d
    @35
    @19
    @38
    c2nd
    @51
    fveq2d
    3brtr4d
    expr
    expcom
    a2d
    nn0ind
    impcom
end
