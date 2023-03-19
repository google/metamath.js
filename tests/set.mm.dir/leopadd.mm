include "cho.mm"
include "wcel.mm"
include "wa.mm"
include "ch0o.mm"
include "cleo.mm"
include "wbr.mm"
include "chos.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "cle.mm"
include "chil.mm"
include "wral.mm"
include "r19.26.mm"
include "caddc.mm"
include "wi.mm"
include "cr.mm"
include "hmopre.mm"
include "addge0.mm"
include "ex.mm"
include "syl2an.mm"
include "anandirs.mm"
include "wf.mm"
include "wceq.mm"
include "hmopf.mm"
include "anim12i.mm"
include "cva.mm"
include "w3a.mm"
include "hosval.mm"
include "oveq1d.mm"
include "3expa.mm"
include "ffvelrn.mm"
include "adantlr.mm"
include "adantll.mm"
include "simpr.mm"
include "ax-his2.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "sylan.mm"
include "breq2d.mm"
include "sylibrd.mm"
include "ralimdva.mm"
include "syl5bir.mm"
include "leoppos.mm"
include "bi2anan9.mm"
include "wb.mm"
include "hmops.mm"
include "syl.mm"
include "3imtr4d.mm"
include "imp.mm"

theorem leopadd
  let cT: class T
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u


  assert |- ( ( ( T e. HrmOp /\ U e. HrmOp ) /\ ( 0hop <_op T /\ 0hop <_op U ) ) -> 0hop <_op ( T +op U ) )

  proof
    cT
    cho
    wcel
    #
    cU
    cho
    wcel
    #
    wa
    #
    ch0o
    cT
    cleo
    wbr
    #
    ch0o
    cU
    cleo
    wbr
    #
    wa
    #
    ch0o
    cT
    cU
    chos
    co
    #
    cleo
    wbr
    #
    @2
    cc0
    vx
    cv
    #
    cT
    cfv
    #
    @8
    csp
    co
    #
    cle
    wbr
    #
    vx
    chil
    wral
    #
    cc0
    @8
    cU
    cfv
    #
    @8
    csp
    co
    #
    cle
    wbr
    #
    vx
    chil
    wral
    #
    wa
    #
    cc0
    @8
    @6
    cfv
    #
    @8
    csp
    co
    #
    cle
    wbr
    #
    vx
    chil
    wral
    #
    @5
    @7
    @17
    @11
    @15
    wa
    #
    vx
    chil
    wral
    @2
    @21
    @11
    @15
    vx
    chil
    r19.26
    @2
    @22
    @20
    vx
    chil
    @2
    @8
    chil
    wcel
    #
    wa
    #
    @22
    cc0
    @10
    @14
    caddc
    co
    #
    cle
    wbr
    #
    @20
    @0
    @1
    @23
    @22
    @26
    wi
    #
    @0
    @23
    wa
    @10
    cr
    wcel
    #
    @14
    cr
    wcel
    #
    @27
    @1
    @23
    wa
    @8
    cT
    hmopre
    @8
    cU
    hmopre
    @28
    @29
    wa
    @22
    @26
    @10
    @14
    addge0
    ex
    syl2an
    anandirs
    @24
    @19
    @25
    cc0
    cle
    @2
    chil
    chil
    cT
    wf
    #
    chil
    chil
    cU
    wf
    #
    wa
    #
    @23
    @19
    @25
    wceq
    @0
    @30
    @1
    @31
    cT
    hmopf
    cU
    hmopf
    anim12i
    @32
    @23
    wa
    #
    @19
    @9
    @13
    cva
    co
    #
    @8
    csp
    co
    #
    @25
    @30
    @31
    @23
    @19
    @35
    wceq
    @30
    @31
    @23
    w3a
    @18
    @34
    @8
    csp
    @8
    cT
    cU
    hosval
    oveq1d
    3expa
    @33
    @9
    chil
    wcel
    #
    @13
    chil
    wcel
    #
    @23
    @35
    @25
    wceq
    @30
    @23
    @36
    @31
    chil
    chil
    @8
    cT
    ffvelrn
    adantlr
    @31
    @23
    @37
    @30
    chil
    chil
    @8
    cU
    ffvelrn
    adantll
    @32
    @23
    simpr
    @9
    @13
    @8
    ax-his2
    syl3anc
    eqtrd
    sylan
    breq2d
    sylibrd
    ralimdva
    syl5bir
    @0
    @3
    @12
    @1
    @4
    @16
    vx
    cT
    leoppos
    vx
    cU
    leoppos
    bi2anan9
    @2
    @6
    cho
    wcel
    @7
    @21
    wb
    cT
    cU
    hmops
    vx
    @6
    leoppos
    syl
    3imtr4d
    imp
end
