include "wbr.mm"
include "wa.mm"
include "cconcat.mm"
include "co.mm"
include "c2o.mm"
include "cxp.mm"
include "cword.mm"
include "cid.mm"
include "cfv.mm"
include "cv.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "c1o.mm"
include "cdif.mm"
include "cop.mm"
include "cmpt2.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "cmpt.mm"
include "crn.mm"
include "ciun.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "c0.mm"
include "csn.mm"
include "crab.mm"
include "eqid.mm"
include "efgcpbl2.mm"
include "cbs.mm"
include "wceq.mm"
include "wer.mm"
include "efger.mm"
include "a1i.mm"
include "simpl.mm"
include "ercl.mm"
include "cvv.mm"
include "efgrcl.mm"
include "syl.mm"
include "simprd.mm"
include "con0.mm"
include "simpld.mm"
include "2on.mm"
include "xpexg.mm"
include "sylancl.mm"
include "frmdbas.mm"
include "eqtr4d.mm"
include "eleqtrd.mm"
include "simpr.mm"
include "frmdadd.mm"
include "syl2anc.mm"
include "ercl2.mm"
include "3brtr4d.mm"

theorem frgpcpbl
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.sm: class .~
  let cG: class G
  let cI: class I
  let cM: class M
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume frgpval.m: |- G = ( freeGrp ` I )
  assume frgpval.b: |- M = ( freeMnd ` ( I X. 2o ) )
  assume frgpval.r: |- .~ = ( ~FG ` I )
  assume frgpcpbl.p: |- .+ = ( +g ` M )


  assert |- ( ( A .~ C /\ B .~ D ) -> ( A .+ B ) .~ ( C .+ D ) )

  proof
    cA
    cC
    c.sm
    wbr
    #
    cB
    cD
    c.sm
    wbr
    #
    wa
    #
    cA
    cB
    cconcat
    co
    #
    cC
    cD
    cconcat
    co
    #
    cA
    cB
    c.pl
    co
    #
    cC
    cD
    c.pl
    co
    #
    c.sm
    vx
    vy
    vz
    vw
    vv
    vt
    cA
    cB
    cI
    c2o
    cxp
    #
    cword
    #
    cid
    cfv
    #
    vx
    @9
    vx
    cv
    vv
    @9
    vn
    vw
    cc0
    vv
    cv
    #
    chash
    cfv
    cfz
    co
    @7
    @10
    vn
    cv
    #
    @11
    vw
    cv
    #
    @12
    vy
    vz
    cI
    c2o
    vy
    cv
    c1o
    vz
    cv
    cdif
    cop
    cmpt2
    #
    cfv
    cs2
    cotp
    csplice
    co
    cmpt2
    cmpt
    #
    cfv
    crn
    ciun
    cdif
    #
    c.sm
    vm
    cc0
    vt
    cv
    #
    cfv
    @15
    wcel
    vk
    cv
    #
    @16
    cfv
    @17
    c1
    cmin
    co
    @16
    cfv
    @14
    cfv
    crn
    wcel
    vk
    c1
    @16
    chash
    cfv
    cfzo
    co
    wral
    wa
    vt
    @9
    cword
    c0
    csn
    cdif
    crab
    vm
    cv
    #
    chash
    cfv
    c1
    cmin
    co
    @18
    cfv
    cmpt
    #
    @14
    vk
    vm
    vn
    cI
    @13
    @9
    cC
    cD
    @9
    eqid
    #
    frgpval.r
    @13
    eqid
    @14
    eqid
    @15
    eqid
    @19
    eqid
    efgcpbl2
    @2
    cA
    cM
    cbs
    cfv
    #
    wcel
    cB
    @21
    wcel
    @5
    @3
    wceq
    @2
    cA
    @9
    @21
    @2
    cA
    cC
    c.sm
    @9
    @9
    c.sm
    wer
    @2
    c.sm
    cI
    @9
    @20
    frgpval.r
    efger
    a1i
    #
    @0
    @1
    simpl
    #
    ercl
    #
    @2
    @9
    @8
    @21
    @2
    cI
    cvv
    wcel
    #
    @9
    @8
    wceq
    #
    @2
    cA
    @9
    wcel
    @25
    @26
    wa
    @24
    cA
    cI
    @9
    @20
    efgrcl
    syl
    #
    simprd
    @2
    @7
    cvv
    wcel
    #
    @21
    @8
    wceq
    @2
    @25
    c2o
    con0
    wcel
    @28
    @2
    @25
    @26
    @27
    simpld
    2on
    cI
    c2o
    cvv
    con0
    xpexg
    sylancl
    @21
    @7
    cM
    cvv
    frgpval.b
    @21
    eqid
    #
    frmdbas
    syl
    eqtr4d
    #
    eleqtrd
    @2
    cB
    @9
    @21
    @2
    cB
    cD
    c.sm
    @9
    @22
    @0
    @1
    simpr
    #
    ercl
    @30
    eleqtrd
    @21
    c.pl
    @7
    cM
    cA
    cB
    frgpval.b
    @29
    frgpcpbl.p
    frmdadd
    syl2anc
    @2
    cC
    @21
    wcel
    cD
    @21
    wcel
    @6
    @4
    wceq
    @2
    cC
    @9
    @21
    @2
    cA
    cC
    c.sm
    @9
    @22
    @23
    ercl2
    @30
    eleqtrd
    @2
    cD
    @9
    @21
    @2
    cB
    cD
    c.sm
    @9
    @22
    @31
    ercl2
    @30
    eleqtrd
    @21
    c.pl
    @7
    cM
    cC
    cD
    frgpval.b
    @29
    frgpcpbl.p
    frmdadd
    syl2anc
    3brtr4d
end
