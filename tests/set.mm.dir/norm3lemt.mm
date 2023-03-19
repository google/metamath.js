include "chil.mm"
include "wcel.mm"
include "cr.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "c2.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "c0v.mm"
include "cif.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi1d.mm"
include "imbi12d.mm"
include "oveq2.mm"
include "anbi2d.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "breq2d.mm"
include "breq2.mm"
include "ifhvhv0.mm"
include "2re.mm"
include "elimel.mm"
include "norm3lem.mm"
include "dedth4h.mm"

theorem norm3lemt
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. ~H /\ B e. ~H ) /\ ( C e. ~H /\ D e. RR ) ) -> ( ( ( normh ` ( A -h C ) ) < ( D / 2 ) /\ ( normh ` ( C -h B ) ) < ( D / 2 ) ) -> ( normh ` ( A -h B ) ) < D ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cC
    chil
    wcel
    #
    cD
    cr
    wcel
    #
    cA
    cC
    cmv
    co
    #
    cno
    cfv
    #
    cD
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    cC
    cB
    cmv
    co
    #
    cno
    cfv
    #
    @6
    clt
    wbr
    #
    wa
    #
    cA
    cB
    cmv
    co
    #
    cno
    cfv
    #
    cD
    clt
    wbr
    #
    wi
    @0
    cA
    c0v
    cif
    #
    cC
    cmv
    co
    #
    cno
    cfv
    #
    @6
    clt
    wbr
    #
    @10
    wa
    #
    @15
    cB
    cmv
    co
    #
    cno
    cfv
    #
    cD
    clt
    wbr
    #
    wi
    @18
    cC
    @1
    cB
    c0v
    cif
    #
    cmv
    co
    #
    cno
    cfv
    #
    @6
    clt
    wbr
    #
    wa
    #
    @15
    @23
    cmv
    co
    #
    cno
    cfv
    #
    cD
    clt
    wbr
    #
    wi
    @15
    @2
    cC
    c0v
    cif
    #
    cmv
    co
    #
    cno
    cfv
    #
    @6
    clt
    wbr
    #
    @31
    @23
    cmv
    co
    #
    cno
    cfv
    #
    @6
    clt
    wbr
    #
    wa
    #
    @30
    wi
    @33
    @3
    cD
    c2
    cif
    #
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    @36
    @40
    clt
    wbr
    #
    wa
    #
    @29
    @39
    clt
    wbr
    #
    wi
    cA
    cB
    cC
    cD
    c0v
    c0v
    c0v
    c2
    cA
    @15
    wceq
    #
    @11
    @19
    @14
    @22
    @45
    @7
    @18
    @10
    @45
    @5
    @17
    @6
    clt
    @45
    @4
    @16
    cno
    cA
    @15
    cC
    cmv
    oveq1
    fveq2d
    breq1d
    anbi1d
    @45
    @13
    @21
    cD
    clt
    @45
    @12
    @20
    cno
    cA
    @15
    cB
    cmv
    oveq1
    fveq2d
    breq1d
    imbi12d
    cB
    @23
    wceq
    #
    @19
    @27
    @22
    @30
    @46
    @10
    @26
    @18
    @46
    @9
    @25
    @6
    clt
    @46
    @8
    @24
    cno
    cB
    @23
    cC
    cmv
    oveq2
    fveq2d
    breq1d
    anbi2d
    @46
    @21
    @29
    cD
    clt
    @46
    @20
    @28
    cno
    cB
    @23
    @15
    cmv
    oveq2
    fveq2d
    breq1d
    imbi12d
    cC
    @31
    wceq
    #
    @27
    @38
    @30
    @47
    @18
    @34
    @26
    @37
    @47
    @17
    @33
    @6
    clt
    @47
    @16
    @32
    cno
    cC
    @31
    @15
    cmv
    oveq2
    fveq2d
    breq1d
    @47
    @25
    @36
    @6
    clt
    @47
    @24
    @35
    cno
    cC
    @31
    @23
    cmv
    oveq1
    fveq2d
    breq1d
    anbi12d
    imbi1d
    cD
    @39
    wceq
    #
    @38
    @43
    @30
    @44
    @48
    @34
    @41
    @37
    @42
    @48
    @6
    @40
    @33
    clt
    cD
    @39
    c2
    cdiv
    oveq1
    #
    breq2d
    @48
    @6
    @40
    @36
    clt
    @49
    breq2d
    anbi12d
    cD
    @39
    @29
    clt
    breq2
    imbi12d
    @15
    @23
    @31
    @39
    cA
    ifhvhv0
    cB
    ifhvhv0
    cC
    ifhvhv0
    cD
    c2
    cr
    2re
    elimel
    norm3lem
    dedth4h
end
