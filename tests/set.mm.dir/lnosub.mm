include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "cns.mm"
include "cfv.mm"
include "co.mm"
include "cpv.mm"
include "wceq.mm"
include "cc.mm"
include "neg1cn.mm"
include "cba.mm"
include "eqid.mm"
include "lnolin.mm"
include "mp3anr1.mm"
include "ancom2s.mm"
include "nvmval2.mm"
include "3expb.mm"
include "3ad2antl1.mm"
include "fveq2d.mm"
include "simpl2.mm"
include "wf.mm"
include "lnof.mm"
include "simpl.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "simpr.mm"
include "syl3anc.mm"
include "3eqtr4d.mm"

theorem lnosub
  let cA: class A
  let cB: class B
  let cT: class T
  let cU: class U
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  assume lnosub.1: |- X = ( BaseSet ` U )
  assume lnosub.5: |- M = ( -v ` U )
  assume lnosub.6: |- N = ( -v ` W )
  assume lnosub.7: |- L = ( U LnOp W )


  assert |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) /\ ( A e. X /\ B e. X ) ) -> ( T ` ( A M B ) ) = ( ( T ` A ) N ( T ` B ) ) )

  proof
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    cT
    cL
    wcel
    #
    w3a
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    wa
    #
    wa
    #
    c1
    cneg
    #
    cB
    cU
    cns
    cfv
    #
    co
    cA
    cU
    cpv
    cfv
    #
    co
    #
    cT
    cfv
    #
    @8
    cB
    cT
    cfv
    #
    cW
    cns
    cfv
    #
    co
    cA
    cT
    cfv
    #
    cW
    cpv
    cfv
    #
    co
    #
    cA
    cB
    cM
    co
    #
    cT
    cfv
    @15
    @13
    cN
    co
    #
    @3
    @5
    @4
    @12
    @17
    wceq
    #
    @3
    @8
    cc
    wcel
    @5
    @4
    @20
    neg1cn
    @8
    cB
    cA
    @9
    @14
    cT
    cU
    @10
    @16
    cL
    cW
    cX
    cW
    cba
    cfv
    #
    lnosub.1
    @21
    eqid
    #
    @10
    eqid
    #
    @16
    eqid
    #
    @9
    eqid
    #
    @14
    eqid
    #
    lnosub.7
    lnolin
    mp3anr1
    ancom2s
    @7
    @18
    @11
    cT
    @0
    @1
    @6
    @18
    @11
    wceq
    #
    @2
    @0
    @4
    @5
    @27
    cA
    cB
    @9
    cU
    @10
    cM
    cX
    lnosub.1
    @23
    @25
    lnosub.5
    nvmval2
    3expb
    3ad2antl1
    fveq2d
    @7
    @1
    @15
    @21
    wcel
    #
    @13
    @21
    wcel
    #
    @19
    @17
    wceq
    @0
    @1
    @2
    @6
    simpl2
    @3
    cX
    @21
    cT
    wf
    #
    @4
    @28
    @6
    cT
    cU
    cL
    cW
    cX
    @21
    lnosub.1
    @22
    lnosub.7
    lnof
    #
    @4
    @5
    simpl
    cX
    @21
    cA
    cT
    ffvelrn
    syl2an
    @3
    @30
    @5
    @29
    @6
    @31
    @4
    @5
    simpr
    cX
    @21
    cB
    cT
    ffvelrn
    syl2an
    @15
    @13
    @14
    cW
    @16
    cN
    @21
    @22
    @24
    @26
    lnosub.6
    nvmval2
    syl3anc
    3eqtr4d
end
