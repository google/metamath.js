include "cn.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprod.mm"
include "wi.mm"
include "c0.mm"
include "cun.mm"
include "cleq1lem.mm"
include "difeq1.mm"
include "raleqdv.mm"
include "raleqbi1dv.mm"
include "raleq.mm"
include "anbi12d.mm"
include "prodeq1.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "prod0.mm"
include "cz.mm"
include "nnz.mm"
include "1dvds.mm"
include "syl.mm"
include "syl5eqbr.mm"
include "adantr.mm"
include "ad2antlr.mm"
include "coprmproddvdslem.mm"
include "findcard2s.mm"
include "exp4c.mm"
include "impcom.mm"
include "3imp.mm"

theorem coprmproddvds
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint F m
  disjoint F n
  disjoint m n
  disjoint K m
  disjoint M m
  disjoint M n
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F x
  disjoint F y
  disjoint F z
  assert |- ( ( ( M C_ NN /\ M e. Fin ) /\ ( K e. NN /\ F : NN --> NN ) /\ ( A. m e. M A. n e. ( M \ { m } ) ( ( F ` m ) gcd ( F ` n ) ) = 1 /\ A. m e. M ( F ` m ) || K ) ) -> prod_ m e. M ( F ` m ) || K )

  proof
    cM
    cn
    wss
    #
    cM
    cfn
    wcel
    #
    wa
    cK
    cn
    wcel
    #
    cn
    cn
    cF
    wf
    #
    wa
    #
    vm
    cv
    #
    cF
    cfv
    #
    vn
    cv
    cF
    cfv
    cgcd
    co
    c1
    wceq
    #
    vn
    cM
    @5
    csn
    #
    cdif
    #
    wral
    #
    vm
    cM
    wral
    #
    @6
    cK
    cdvds
    wbr
    #
    vm
    cM
    wral
    #
    wa
    #
    cM
    @6
    vm
    cprod
    #
    cK
    cdvds
    wbr
    #
    @1
    @0
    @4
    @14
    @16
    wi
    wi
    @1
    @0
    @4
    @14
    @16
    vx
    cv
    #
    cn
    wss
    @4
    wa
    #
    @7
    vn
    @17
    @8
    cdif
    #
    wral
    #
    vm
    @17
    wral
    #
    @12
    vm
    @17
    wral
    #
    wa
    #
    wa
    #
    @17
    @6
    vm
    cprod
    #
    cK
    cdvds
    wbr
    #
    wi
    c0
    cn
    wss
    #
    @4
    wa
    #
    @7
    vn
    c0
    @8
    cdif
    #
    wral
    #
    vm
    c0
    wral
    #
    @12
    vm
    c0
    wral
    #
    wa
    #
    wa
    #
    c0
    @6
    vm
    cprod
    #
    cK
    cdvds
    wbr
    #
    wi
    vy
    cv
    #
    cn
    wss
    @4
    wa
    #
    @7
    vn
    @37
    @8
    cdif
    #
    wral
    #
    vm
    @37
    wral
    #
    @12
    vm
    @37
    wral
    #
    wa
    #
    wa
    #
    @37
    @6
    vm
    cprod
    #
    cK
    cdvds
    wbr
    #
    wi
    @37
    vz
    cv
    csn
    cun
    #
    cn
    wss
    @4
    wa
    #
    @7
    vn
    @47
    @8
    cdif
    #
    wral
    #
    vm
    @47
    wral
    #
    @12
    vm
    @47
    wral
    #
    wa
    #
    wa
    #
    @47
    @6
    vm
    cprod
    #
    cK
    cdvds
    wbr
    #
    wi
    @0
    @4
    wa
    #
    @14
    wa
    #
    @16
    wi
    vx
    vy
    vz
    cM
    @17
    c0
    wceq
    #
    @24
    @34
    @26
    @36
    @59
    @18
    @28
    @23
    @33
    @4
    @17
    c0
    cn
    cleq1lem
    @59
    @21
    @31
    @22
    @32
    @20
    @30
    vm
    @17
    c0
    @59
    @7
    vn
    @19
    @29
    @17
    c0
    @8
    difeq1
    raleqdv
    raleqbi1dv
    @12
    vm
    @17
    c0
    raleq
    anbi12d
    anbi12d
    @59
    @25
    @35
    cK
    cdvds
    @17
    c0
    @6
    vm
    prodeq1
    breq1d
    imbi12d
    @17
    @37
    wceq
    #
    @24
    @44
    @26
    @46
    @60
    @18
    @38
    @23
    @43
    @4
    @17
    @37
    cn
    cleq1lem
    @60
    @21
    @41
    @22
    @42
    @20
    @40
    vm
    @17
    @37
    @60
    @7
    vn
    @19
    @39
    @17
    @37
    @8
    difeq1
    raleqdv
    raleqbi1dv
    @12
    vm
    @17
    @37
    raleq
    anbi12d
    anbi12d
    @60
    @25
    @45
    cK
    cdvds
    @17
    @37
    @6
    vm
    prodeq1
    breq1d
    imbi12d
    @17
    @47
    wceq
    #
    @24
    @54
    @26
    @56
    @61
    @18
    @48
    @23
    @53
    @4
    @17
    @47
    cn
    cleq1lem
    @61
    @21
    @51
    @22
    @52
    @20
    @50
    vm
    @17
    @47
    @61
    @7
    vn
    @19
    @49
    @17
    @47
    @8
    difeq1
    raleqdv
    raleqbi1dv
    @12
    vm
    @17
    @47
    raleq
    anbi12d
    anbi12d
    @61
    @25
    @55
    cK
    cdvds
    @17
    @47
    @6
    vm
    prodeq1
    breq1d
    imbi12d
    @17
    cM
    wceq
    #
    @24
    @58
    @26
    @16
    @62
    @18
    @57
    @23
    @14
    @4
    @17
    cM
    cn
    cleq1lem
    @62
    @21
    @11
    @22
    @13
    @20
    @10
    vm
    @17
    cM
    @62
    @7
    vn
    @19
    @9
    @17
    cM
    @8
    difeq1
    raleqdv
    raleqbi1dv
    @12
    vm
    @17
    cM
    raleq
    anbi12d
    anbi12d
    @62
    @25
    @15
    cK
    cdvds
    @17
    cM
    @6
    vm
    prodeq1
    breq1d
    imbi12d
    @4
    @36
    @27
    @33
    @2
    @36
    @3
    @2
    @35
    c1
    cK
    cdvds
    @6
    vm
    prod0
    @2
    cK
    cz
    wcel
    c1
    cK
    cdvds
    wbr
    cK
    nnz
    cK
    1dvds
    syl
    syl5eqbr
    adantr
    ad2antlr
    vy
    vz
    vm
    vn
    cF
    cK
    coprmproddvdslem
    findcard2s
    exp4c
    impcom
    3imp
end
