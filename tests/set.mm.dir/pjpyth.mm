include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cno.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cpjh.mm"
include "cort.mm"
include "caddc.mm"
include "wceq.mm"
include "cif.mm"
include "c0v.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "eqeq12d.mm"
include "ifchhv.mm"
include "ifhvhv0.mm"
include "pjpythi.mm"
include "dedth2h.mm"

theorem pjpyth
  let cA: class A
  let cH: class H


  assert |- ( ( H e. CH /\ A e. ~H ) -> ( ( normh ` A ) ^ 2 ) = ( ( ( normh ` ( ( projh ` H ) ` A ) ) ^ 2 ) + ( ( normh ` ( ( projh ` ( _|_ ` H ) ) ` A ) ) ^ 2 ) ) )

  proof
    cH
    cch
    wcel
    #
    cA
    chil
    wcel
    #
    cA
    cno
    cfv
    #
    c2
    cexp
    co
    #
    cA
    cH
    cpjh
    cfv
    #
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    cA
    cH
    cort
    cfv
    #
    cpjh
    cfv
    #
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    @3
    cA
    @0
    cH
    chil
    cif
    #
    cpjh
    cfv
    #
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    cA
    @14
    cort
    cfv
    #
    cpjh
    cfv
    #
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    @1
    cA
    c0v
    cif
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @25
    @15
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @25
    @20
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    cH
    cA
    chil
    c0v
    cH
    @14
    wceq
    #
    @13
    @24
    @3
    @35
    @7
    @18
    @12
    @23
    caddc
    @35
    @6
    @17
    c2
    cexp
    @35
    @5
    @16
    cno
    @35
    cA
    @4
    @15
    cH
    @14
    cpjh
    fveq2
    fveq1d
    fveq2d
    oveq1d
    @35
    @11
    @22
    c2
    cexp
    @35
    @10
    @21
    cno
    @35
    cA
    @9
    @20
    @35
    @8
    @19
    cpjh
    cH
    @14
    cort
    fveq2
    fveq2d
    fveq1d
    fveq2d
    oveq1d
    oveq12d
    eqeq2d
    cA
    @25
    wceq
    #
    @3
    @27
    @24
    @34
    @36
    @2
    @26
    c2
    cexp
    cA
    @25
    cno
    fveq2
    oveq1d
    @36
    @18
    @30
    @23
    @33
    caddc
    @36
    @17
    @29
    c2
    cexp
    @36
    @16
    @28
    cno
    cA
    @25
    @15
    fveq2
    fveq2d
    oveq1d
    @36
    @22
    @32
    c2
    cexp
    @36
    @21
    @31
    cno
    cA
    @25
    @20
    fveq2
    fveq2d
    oveq1d
    oveq12d
    eqeq12d
    @25
    @14
    cH
    ifchhv
    cA
    ifhvhv0
    pjpythi
    dedth2h
end
