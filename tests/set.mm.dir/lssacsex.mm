include "clvec.mm"
include "wcel.mm"
include "cacs.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cun.mm"
include "cdif.mm"
include "wral.mm"
include "cpw.mm"
include "clmod.mm"
include "lveclmod.mm"
include "lssacs.mm"
include "syl.mm"
include "wa.mm"
include "clspn.mm"
include "wss.mm"
include "simplll.mm"
include "simpllr.mm"
include "elpwid.mm"
include "simplr.mm"
include "simpr.mm"
include "wceq.mm"
include "eqid.mm"
include "mrclsp.mm"
include "3syl.mm"
include "fveq1d.mm"
include "difeq12d.mm"
include "eleqtrrd.mm"
include "lspsolv.mm"
include "syl13anc.mm"
include "eleqtrd.mm"
include "ralrimiva.mm"
include "jca.mm"

theorem lssacsex
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cN: class N
  let cW: class W
  let cX: class X
  let vs: setvar s
  assume lssacsex.1: |- A = ( LSubSp ` W )
  assume lssacsex.2: |- N = ( mrCls ` A )
  assume lssacsex.3: |- X = ( Base ` W )

  disjoint W s
  disjoint s y
  disjoint s z
  disjoint W y
  disjoint W z
  disjoint y z
  disjoint X y
  disjoint X z
  assert |- ( W e. LVec -> ( A e. ( ACS ` X ) /\ A. s e. ~P X A. y e. X A. z e. ( ( N ` ( s u. { y } ) ) \ ( N ` s ) ) y e. ( N ` ( s u. { z } ) ) ) )

  proof
    cW
    clvec
    wcel
    #
    cA
    cX
    cacs
    cfv
    wcel
    #
    vy
    cv
    #
    vs
    cv
    #
    vz
    cv
    #
    csn
    cun
    #
    cN
    cfv
    #
    wcel
    #
    vz
    @3
    @2
    csn
    cun
    #
    cN
    cfv
    #
    @3
    cN
    cfv
    #
    cdif
    #
    wral
    #
    vy
    cX
    wral
    #
    vs
    cX
    cpw
    #
    wral
    @0
    cW
    clmod
    wcel
    #
    @1
    cW
    lveclmod
    #
    cX
    cA
    cW
    lssacsex.3
    lssacsex.1
    lssacs
    syl
    @0
    @13
    vs
    @14
    @0
    @3
    @14
    wcel
    #
    wa
    #
    @12
    vy
    cX
    @18
    @2
    cX
    wcel
    #
    wa
    #
    @7
    vz
    @11
    @20
    @4
    @11
    wcel
    #
    wa
    #
    @2
    @5
    cW
    clspn
    cfv
    #
    cfv
    #
    @6
    @22
    @0
    @3
    cX
    wss
    @19
    @4
    @8
    @23
    cfv
    #
    @3
    @23
    cfv
    #
    cdif
    #
    wcel
    @2
    @24
    wcel
    @0
    @17
    @19
    @21
    simplll
    #
    @22
    @3
    cX
    @0
    @17
    @19
    @21
    simpllr
    elpwid
    @18
    @19
    @21
    simplr
    @22
    @4
    @11
    @27
    @20
    @21
    simpr
    @22
    @25
    @9
    @26
    @10
    @22
    @8
    @23
    cN
    @22
    @0
    @15
    @23
    cN
    wceq
    @28
    @16
    cA
    cN
    @23
    cW
    lssacsex.1
    @23
    eqid
    #
    lssacsex.2
    mrclsp
    3syl
    #
    fveq1d
    @22
    @3
    @23
    cN
    @30
    fveq1d
    difeq12d
    eleqtrrd
    @3
    cA
    @23
    cX
    cW
    @4
    @2
    lssacsex.3
    lssacsex.1
    @29
    lspsolv
    syl13anc
    @22
    @5
    @23
    cN
    @30
    fveq1d
    eleqtrd
    ralrimiva
    ralrimiva
    ralrimiva
    jca
end
