include "cop.mm"
include "co.mm"
include "cr.mm"
include "cxp.mm"
include "wcel.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "wceq.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cv.mm"
include "csb.mm"
include "cmpt2.mm"
include "oveqd.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "wa.mm"
include "simpr.mm"
include "breq2d.mm"
include "simpl.mm"
include "fveq2d.mm"
include "opeq1d.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "opeq12d.mm"
include "ifbieq12d.mm"
include "csbeq2dv.mm"
include "oveq12d.mm"
include "csbeq1d.mm"
include "eqtrd.mm"
include "eqid.mm"
include "opex.mm"
include "ifex.mm"
include "csbex.mm"
include "ovmpt2a.mm"
include "op1stg.mm"
include "op2ndg.mm"
include "ovex.mm"
include "breq1.mm"
include "opeq2.mm"
include "oveq1.mm"
include "csbie.mm"
include "ifeq12d.mm"
include "syl5eq.mm"
include "readdcld.mm"
include "rehalfcld.mm"
include "ifcld.mm"
include "eqeltrd.mm"
include "fvif.mm"
include "cvv.mm"
include "sylancl.mm"
include "sylancr.mm"
include "3jca.mm"

theorem ruclem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let vm: setvar m
  let cF: class F
  let cM: class M
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vz: setvar z
  let cC: class C
  let vn: setvar n
  let vk: setvar k
  let cG: class G
  let cN: class N
  let cS: class S
  assume ruc.1: |- ( ph -> F : NN --> RR )
  assume ruc.2: |- ( ph -> D = ( x e. ( RR X. RR ) , y e. RR |-> [_ ( ( ( 1st ` x ) + ( 2nd ` x ) ) / 2 ) / m ]_ if ( m < y , <. ( 1st ` x ) , m >. , <. ( ( m + ( 2nd ` x ) ) / 2 ) , ( 2nd ` x ) >. ) ) )
  assume ruclem1.3: |- ( ph -> A e. RR )
  assume ruclem1.4: |- ( ph -> B e. RR )
  assume ruclem1.5: |- ( ph -> M e. RR )
  assume ruclem1.6: |- X = ( 1st ` ( <. A , B >. D M ) )
  assume ruclem1.7: |- Y = ( 2nd ` ( <. A , B >. D M ) )

  disjoint m x
  disjoint m y
  disjoint x y
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint M m
  disjoint M x
  disjoint M y
  disjoint m w
  disjoint w x
  disjoint w y
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
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint M k
  disjoint M n
  disjoint N k
  disjoint N m
  disjoint N x
  disjoint N y
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
  assert |- ( ph -> ( ( <. A , B >. D M ) e. ( RR X. RR ) /\ X = if ( ( ( A + B ) / 2 ) < M , A , ( ( ( ( A + B ) / 2 ) + B ) / 2 ) ) /\ Y = if ( ( ( A + B ) / 2 ) < M , ( ( A + B ) / 2 ) , B ) ) )

  proof
    wph
    cA
    cB
    cop
    #
    cM
    cD
    co
    #
    cr
    cr
    cxp
    #
    wcel
    cX
    cA
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cM
    clt
    wbr
    #
    cA
    @4
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cif
    #
    wceq
    cY
    @5
    @4
    cB
    cif
    #
    wceq
    wph
    @1
    @5
    cA
    @4
    cop
    #
    @7
    cB
    cop
    #
    cif
    #
    @2
    wph
    @1
    vm
    @0
    c1st
    cfv
    #
    @0
    c2nd
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    vm
    cv
    #
    cM
    clt
    wbr
    #
    @13
    @17
    cop
    #
    @17
    @14
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @14
    cop
    #
    cif
    #
    csb
    #
    @12
    wph
    @1
    @0
    cM
    vx
    vy
    @2
    cr
    vm
    vx
    cv
    #
    c1st
    cfv
    #
    @25
    c2nd
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @17
    vy
    cv
    #
    clt
    wbr
    #
    @26
    @17
    cop
    #
    @17
    @27
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @27
    cop
    #
    cif
    #
    csb
    #
    cmpt2
    #
    co
    #
    @24
    wph
    cD
    @38
    @0
    cM
    ruc.2
    oveqd
    wph
    @0
    @2
    wcel
    #
    cM
    cr
    wcel
    @39
    @24
    wceq
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @40
    ruclem1.3
    ruclem1.4
    cA
    cB
    cr
    cr
    opelxpi
    syl2anc
    ruclem1.5
    vx
    vy
    @0
    cM
    @2
    cr
    @37
    @24
    @38
    @25
    @0
    wceq
    #
    @30
    cM
    wceq
    #
    wa
    #
    @37
    vm
    @29
    @23
    csb
    @24
    @45
    vm
    @29
    @36
    @23
    @45
    @31
    @18
    @32
    @35
    @19
    @22
    @45
    @30
    cM
    @17
    clt
    @43
    @44
    simpr
    breq2d
    @45
    @26
    @13
    @17
    @45
    @25
    @0
    c1st
    @43
    @44
    simpl
    #
    fveq2d
    #
    opeq1d
    @45
    @34
    @21
    @27
    @14
    @45
    @33
    @20
    c2
    cdiv
    @45
    @27
    @14
    @17
    caddc
    @45
    @25
    @0
    c2nd
    @46
    fveq2d
    #
    oveq2d
    oveq1d
    @48
    opeq12d
    ifbieq12d
    csbeq2dv
    @45
    vm
    @29
    @16
    @23
    @45
    @28
    @15
    c2
    cdiv
    @45
    @26
    @13
    @27
    @14
    caddc
    @47
    @48
    oveq12d
    oveq1d
    csbeq1d
    eqtrd
    @38
    eqid
    vm
    @16
    @23
    @18
    @19
    @22
    @13
    @17
    opex
    @21
    @14
    opex
    ifex
    csbex
    ovmpt2a
    syl2anc
    eqtrd
    wph
    @24
    vm
    @4
    @23
    csb
    #
    @12
    wph
    vm
    @16
    @4
    @23
    wph
    @15
    @3
    c2
    cdiv
    wph
    @13
    cA
    @14
    cB
    caddc
    wph
    @41
    @42
    @13
    cA
    wceq
    ruclem1.3
    ruclem1.4
    cA
    cB
    cr
    cr
    op1stg
    syl2anc
    #
    wph
    @41
    @42
    @14
    cB
    wceq
    ruclem1.3
    ruclem1.4
    cA
    cB
    cr
    cr
    op2ndg
    syl2anc
    #
    oveq12d
    oveq1d
    csbeq1d
    wph
    @49
    @5
    @13
    @4
    cop
    #
    @4
    @14
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @14
    cop
    #
    cif
    #
    @12
    vm
    @4
    @23
    @56
    @3
    c2
    cdiv
    ovex
    #
    @17
    @4
    wceq
    #
    @18
    @5
    @19
    @22
    @52
    @55
    @17
    @4
    cM
    clt
    breq1
    @17
    @4
    @13
    opeq2
    @58
    @21
    @54
    @14
    @58
    @20
    @53
    c2
    cdiv
    @17
    @4
    @14
    caddc
    oveq1
    oveq1d
    opeq1d
    ifbieq12d
    csbie
    wph
    @5
    @52
    @10
    @55
    @11
    wph
    @13
    cA
    @4
    @50
    opeq1d
    wph
    @54
    @7
    @14
    cB
    wph
    @53
    @6
    c2
    cdiv
    wph
    @14
    cB
    @4
    caddc
    @51
    oveq2d
    oveq1d
    @51
    opeq12d
    ifeq12d
    syl5eq
    eqtrd
    eqtrd
    #
    wph
    @5
    @10
    @11
    @2
    wph
    @41
    @4
    cr
    wcel
    @10
    @2
    wcel
    ruclem1.3
    wph
    @3
    wph
    cA
    cB
    ruclem1.3
    ruclem1.4
    readdcld
    rehalfcld
    #
    cA
    @4
    cr
    cr
    opelxpi
    syl2anc
    wph
    @7
    cr
    wcel
    @42
    @11
    @2
    wcel
    wph
    @6
    wph
    @4
    cB
    @60
    ruclem1.4
    readdcld
    rehalfcld
    ruclem1.4
    @7
    cB
    cr
    cr
    opelxpi
    syl2anc
    ifcld
    eqeltrd
    wph
    cX
    @1
    c1st
    cfv
    #
    @8
    ruclem1.6
    wph
    @61
    @12
    c1st
    cfv
    #
    @8
    wph
    @1
    @12
    c1st
    @59
    fveq2d
    wph
    @62
    @5
    @10
    c1st
    cfv
    #
    @11
    c1st
    cfv
    #
    cif
    @8
    @5
    @10
    @11
    c1st
    fvif
    wph
    @5
    @63
    cA
    @64
    @7
    wph
    @41
    @4
    cvv
    wcel
    #
    @63
    cA
    wceq
    ruclem1.3
    @57
    cA
    @4
    cr
    cvv
    op1stg
    sylancl
    wph
    @7
    cvv
    wcel
    #
    @42
    @64
    @7
    wceq
    @6
    c2
    cdiv
    ovex
    #
    ruclem1.4
    @7
    cB
    cvv
    cr
    op1stg
    sylancr
    ifeq12d
    syl5eq
    eqtrd
    syl5eq
    wph
    cY
    @1
    c2nd
    cfv
    #
    @9
    ruclem1.7
    wph
    @68
    @12
    c2nd
    cfv
    #
    @9
    wph
    @1
    @12
    c2nd
    @59
    fveq2d
    wph
    @69
    @5
    @10
    c2nd
    cfv
    #
    @11
    c2nd
    cfv
    #
    cif
    @9
    @5
    @10
    @11
    c2nd
    fvif
    wph
    @5
    @70
    @4
    @71
    cB
    wph
    @41
    @65
    @70
    @4
    wceq
    ruclem1.3
    @57
    cA
    @4
    cr
    cvv
    op2ndg
    sylancl
    wph
    @66
    @42
    @71
    cB
    wceq
    @67
    ruclem1.4
    @7
    cB
    cvv
    cr
    op2ndg
    sylancr
    ifeq12d
    syl5eq
    eqtrd
    syl5eq
    3jca
end
