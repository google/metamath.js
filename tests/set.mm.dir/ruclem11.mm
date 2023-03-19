include "c1st.mm"
include "ccom.mm"
include "crn.mm"
include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cn0.mm"
include "wf.mm"
include "cxp.mm"
include "ruclem6.mm"
include "1stcof.mm"
include "syl.mm"
include "frn.mm"
include "cdm.mm"
include "wceq.mm"
include "fdm.mm"
include "cc0.mm"
include "wcel.mm"
include "0nn0.mm"
include "ne0i.mm"
include "mp1i.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "sylib.mm"
include "cfv.mm"
include "wa.mm"
include "fvco3.mm"
include "sylan.mm"
include "clt.mm"
include "c2nd.mm"
include "cn.mm"
include "adantr.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cop.mm"
include "cif.mm"
include "csb.mm"
include "cmpt2.mm"
include "simpr.mm"
include "a1i.mm"
include "ruclem10.mm"
include "ruclem4.mm"
include "fveq2d.mm"
include "c0ex.mm"
include "1ex.mm"
include "op2nd.mm"
include "syl6eq.mm"
include "breqtrd.mm"
include "wi.mm"
include "ffvelrnda.mm"
include "xp1st.mm"
include "1re.mm"
include "ltle.mm"
include "sylancl.mm"
include "mpd.mm"
include "eqbrtrd.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "breq1.mm"
include "ralrn.mm"
include "mpbird.mm"
include "3jca.mm"

theorem ruclem11
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D
  let vm: setvar m
  let cF: class F
  let cG: class G
  let vw: setvar w
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vk: setvar k
  let cM: class M
  let cN: class N
  let cS: class S
  assume ruc.1: |- ( ph -> F : NN --> RR )
  assume ruc.2: |- ( ph -> D = ( x e. ( RR X. RR ) , y e. RR |-> [_ ( ( ( 1st ` x ) + ( 2nd ` x ) ) / 2 ) / m ]_ if ( m < y , <. ( 1st ` x ) , m >. , <. ( ( m + ( 2nd ` x ) ) / 2 ) , ( 2nd ` x ) >. ) ) )
  assume ruc.4: |- C = ( { <. 0 , <. 0 , 1 >. >. } u. F )
  assume ruc.5: |- G = seq 0 ( D , C )

  disjoint m x
  disjoint m y
  disjoint x y
  disjoint C z
  disjoint m z
  disjoint F m
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G m
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph z
  disjoint D z
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
  disjoint m n
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint G k
  disjoint G n
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint N k
  disjoint N m
  disjoint N x
  disjoint N y
  disjoint k w
  disjoint k ph
  disjoint n w
  disjoint n ph
  disjoint ph w
  disjoint D w
  disjoint S n
  disjoint S z
  assert |- ( ph -> ( ran ( 1st o. G ) C_ RR /\ ran ( 1st o. G ) =/= (/) /\ A. z e. ran ( 1st o. G ) z <_ 1 ) )

  proof
    wph
    c1st
    cG
    ccom
    #
    crn
    #
    cr
    wss
    #
    @1
    c0
    wne
    #
    vz
    cv
    #
    c1
    cle
    wbr
    #
    vz
    @1
    wral
    #
    wph
    cn0
    cr
    @0
    wf
    #
    @2
    wph
    cn0
    cr
    cr
    cxp
    #
    cG
    wf
    #
    @7
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
    cn0
    cr
    cr
    cG
    1stcof
    syl
    #
    cn0
    cr
    @0
    frn
    syl
    wph
    @0
    cdm
    #
    c0
    wne
    @3
    wph
    @12
    cn0
    c0
    wph
    @7
    @12
    cn0
    wceq
    @11
    cn0
    cr
    @0
    fdm
    syl
    cc0
    cn0
    wcel
    #
    cn0
    c0
    wne
    wph
    0nn0
    cn0
    cc0
    ne0i
    mp1i
    eqnetrd
    @12
    c0
    @1
    c0
    @0
    dm0rn0
    necon3bii
    sylib
    wph
    @6
    vn
    cv
    #
    @0
    cfv
    #
    c1
    cle
    wbr
    #
    vn
    cn0
    wral
    #
    wph
    @16
    vn
    cn0
    wph
    @14
    cn0
    wcel
    #
    wa
    #
    @15
    @14
    cG
    cfv
    #
    c1st
    cfv
    #
    c1
    cle
    wph
    @9
    @18
    @15
    @21
    wceq
    @10
    cn0
    @8
    @14
    c1st
    cG
    fvco3
    sylan
    @19
    @21
    c1
    clt
    wbr
    #
    @21
    c1
    cle
    wbr
    #
    @19
    @21
    cc0
    cG
    cfv
    #
    c2nd
    cfv
    #
    c1
    clt
    @19
    vx
    vy
    cC
    cD
    vm
    cF
    cG
    @14
    cc0
    wph
    cn
    cr
    cF
    wf
    @18
    ruc.1
    adantr
    wph
    cD
    vx
    vy
    @8
    cr
    vm
    vx
    cv
    #
    c1st
    cfv
    #
    @26
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
    @27
    @29
    cop
    @29
    @28
    caddc
    co
    c2
    cdiv
    co
    @28
    cop
    cif
    csb
    cmpt2
    wceq
    @18
    ruc.2
    adantr
    ruc.4
    ruc.5
    wph
    @18
    simpr
    @13
    @19
    0nn0
    a1i
    ruclem10
    wph
    @25
    c1
    wceq
    @18
    wph
    @25
    cc0
    c1
    cop
    #
    c2nd
    cfv
    c1
    wph
    @24
    @30
    c2nd
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
    fveq2d
    cc0
    c1
    c0ex
    1ex
    op2nd
    syl6eq
    adantr
    breqtrd
    @19
    @21
    cr
    wcel
    #
    c1
    cr
    wcel
    @22
    @23
    wi
    @19
    @20
    @8
    wcel
    @31
    wph
    cn0
    @8
    @14
    cG
    @10
    ffvelrnda
    @20
    cr
    cr
    xp1st
    syl
    1re
    @21
    c1
    ltle
    sylancl
    mpd
    eqbrtrd
    ralrimiva
    wph
    @0
    cn0
    wfn
    #
    @6
    @17
    wb
    wph
    @7
    @32
    @11
    cn0
    cr
    @0
    ffn
    syl
    @5
    @16
    vz
    vn
    cn0
    @0
    @4
    @15
    c1
    cle
    breq1
    ralrn
    syl
    mpbird
    3jca
end
