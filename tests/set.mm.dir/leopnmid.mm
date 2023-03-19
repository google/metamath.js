include "cho.mm"
include "wcel.mm"
include "cnop.mm"
include "cfv.mm"
include "cr.mm"
include "wa.mm"
include "chio.mm"
include "chot.mm"
include "co.mm"
include "cleo.mm"
include "wbr.mm"
include "cv.mm"
include "csp.mm"
include "cle.mm"
include "chil.mm"
include "wral.mm"
include "cabs.mm"
include "hmopre.mm"
include "adantlr.mm"
include "recnd.mm"
include "abscld.mm"
include "idhmop.mm"
include "hmopm.mm"
include "mpan2.mm"
include "sylan.mm"
include "adantll.mm"
include "leabsd.mm"
include "cno.mm"
include "cmul.mm"
include "wf.mm"
include "hmopf.mm"
include "ffvelrn.mm"
include "normcl.mm"
include "syl.mm"
include "adantl.mm"
include "remulcld.mm"
include "bcs.mm"
include "sylancom.mm"
include "cc0.mm"
include "remulcl.mm"
include "sylan2.mm"
include "normge0.mm"
include "jca.mm"
include "cbo.mm"
include "clo.mm"
include "hmoplin.mm"
include "elbdop2.mm"
include "biimpri.mm"
include "nmbdoplb.mm"
include "lemul1a.mm"
include "syl31anc.mm"
include "csm.mm"
include "cc.mm"
include "recn.mm"
include "ad2antlr.mm"
include "mulassd.mm"
include "wceq.mm"
include "simpr.mm"
include "ax-his3.mm"
include "syl3anc.mm"
include "c2.mm"
include "cexp.mm"
include "sqvald.mm"
include "normsq.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "wf1o.mm"
include "hoif.mm"
include "f1of.mm"
include "mp1i.mm"
include "homval.mm"
include "hoival.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "breqtrd.mm"
include "letrd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "leop2.mm"
include "mpbird.mm"

theorem leopnmid
  let cT: class T
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
  let cU: class U


  assert |- ( ( T e. HrmOp /\ ( normop ` T ) e. RR ) -> T <_op ( ( normop ` T ) .op Iop ) )

  proof
    cT
    cho
    wcel
    #
    cT
    cnop
    cfv
    #
    cr
    wcel
    #
    wa
    #
    cT
    @1
    chio
    chot
    co
    #
    cleo
    wbr
    #
    vx
    cv
    #
    cT
    cfv
    #
    @6
    csp
    co
    #
    @6
    @4
    cfv
    #
    @6
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
    @3
    @11
    vx
    chil
    @3
    @6
    chil
    wcel
    #
    wa
    #
    @8
    @8
    cabs
    cfv
    #
    @10
    @0
    @13
    @8
    cr
    wcel
    @2
    @6
    cT
    hmopre
    #
    adantlr
    @0
    @13
    @15
    cr
    wcel
    @2
    @0
    @13
    wa
    #
    @8
    @17
    @8
    @16
    recnd
    abscld
    adantlr
    #
    @2
    @13
    @10
    cr
    wcel
    #
    @0
    @2
    @4
    cho
    wcel
    #
    @13
    @19
    @2
    chio
    cho
    wcel
    @20
    idhmop
    @1
    chio
    hmopm
    mpan2
    #
    @6
    @4
    hmopre
    sylan
    adantll
    #
    @0
    @13
    @8
    @15
    cle
    wbr
    @2
    @17
    @8
    @16
    leabsd
    adantlr
    @14
    @15
    @7
    cno
    cfv
    #
    @6
    cno
    cfv
    #
    cmul
    co
    #
    @10
    @18
    @14
    @23
    @24
    @0
    @13
    @23
    cr
    wcel
    #
    @2
    @0
    chil
    chil
    cT
    wf
    #
    @13
    @26
    cT
    hmopf
    #
    @27
    @13
    wa
    @7
    chil
    wcel
    #
    @26
    chil
    chil
    @6
    cT
    ffvelrn
    #
    @7
    normcl
    syl
    sylan
    adantlr
    #
    @13
    @24
    cr
    wcel
    #
    @3
    @6
    normcl
    #
    adantl
    #
    remulcld
    @22
    @0
    @13
    @15
    @25
    cle
    wbr
    #
    @2
    @0
    @13
    @29
    @35
    @0
    @27
    @13
    @29
    @28
    @30
    sylan
    @7
    @6
    bcs
    sylancom
    adantlr
    @14
    @25
    @1
    @24
    cmul
    co
    #
    @24
    cmul
    co
    #
    @10
    cle
    @14
    @26
    @36
    cr
    wcel
    #
    @32
    cc0
    @24
    cle
    wbr
    #
    wa
    #
    @23
    @36
    cle
    wbr
    #
    @25
    @37
    cle
    wbr
    @31
    @2
    @13
    @38
    @0
    @13
    @2
    @32
    @38
    @33
    @1
    @24
    remulcl
    sylan2
    adantll
    @13
    @40
    @3
    @13
    @32
    @39
    @33
    @6
    normge0
    jca
    adantl
    @3
    cT
    cbo
    wcel
    #
    @13
    @41
    @0
    cT
    clo
    wcel
    #
    @2
    @42
    cT
    hmoplin
    @42
    @43
    @2
    wa
    cT
    elbdop2
    biimpri
    sylan
    @6
    cT
    nmbdoplb
    sylan
    @23
    @36
    @24
    lemul1a
    syl31anc
    @14
    @37
    @1
    @6
    csm
    co
    #
    @6
    csp
    co
    #
    @10
    @14
    @37
    @1
    @24
    @24
    cmul
    co
    #
    cmul
    co
    #
    @45
    @14
    @1
    @24
    @24
    @2
    @1
    cc
    wcel
    #
    @0
    @13
    @1
    recn
    ad2antlr
    #
    @14
    @24
    @34
    recnd
    #
    @50
    mulassd
    @14
    @45
    @1
    @6
    @6
    csp
    co
    #
    cmul
    co
    #
    @47
    @14
    @48
    @13
    @13
    @45
    @52
    wceq
    @49
    @3
    @13
    simpr
    #
    @53
    @1
    @6
    @6
    ax-his3
    syl3anc
    @13
    @47
    @52
    wceq
    @3
    @13
    @46
    @51
    @1
    cmul
    @13
    @24
    c2
    cexp
    co
    @46
    @51
    @13
    @24
    @13
    @24
    @33
    recnd
    sqvald
    @6
    normsq
    eqtr3d
    oveq2d
    adantl
    eqtr4d
    eqtr4d
    @14
    @9
    @44
    @6
    csp
    @14
    @9
    @1
    @6
    chio
    cfv
    #
    csm
    co
    #
    @44
    @14
    @48
    chil
    chil
    chio
    wf
    #
    @13
    @9
    @55
    wceq
    @49
    chil
    chil
    chio
    wf1o
    @56
    @14
    hoif
    chil
    chil
    chio
    f1of
    mp1i
    @53
    @1
    @6
    chio
    homval
    syl3anc
    @13
    @55
    @44
    wceq
    @3
    @13
    @54
    @6
    @1
    csm
    @6
    hoival
    oveq2d
    adantl
    eqtrd
    oveq1d
    eqtr4d
    breqtrd
    letrd
    letrd
    ralrimiva
    @2
    @0
    @20
    @5
    @12
    wb
    @21
    vx
    cT
    @4
    leop2
    sylan2
    mpbird
end
