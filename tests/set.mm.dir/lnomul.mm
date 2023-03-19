include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "cc.mm"
include "wa.mm"
include "co.mm"
include "cn0v.mm"
include "cfv.mm"
include "cpv.mm"
include "wceq.mm"
include "simpl.mm"
include "simprl.mm"
include "simprr.mm"
include "simpl1.mm"
include "eqid.mm"
include "nvzcl.mm"
include "syl.mm"
include "cba.mm"
include "lnolin.mm"
include "syl13anc.mm"
include "nvscl.mm"
include "syl3anc.mm"
include "nv0rid.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "lno0.mm"
include "oveq2d.mm"
include "adantr.mm"
include "simpl2.mm"
include "wf.mm"
include "lnof.mm"
include "ffvelrnd.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem lnomul
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cL: class L
  let cW: class W
  let cX: class X
  assume lnomul.1: |- X = ( BaseSet ` U )
  assume lnomul.5: |- R = ( .sOLD ` U )
  assume lnomul.6: |- S = ( .sOLD ` W )
  assume lnomul.7: |- L = ( U LnOp W )


  assert |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) /\ ( A e. CC /\ B e. X ) ) -> ( T ` ( A R B ) ) = ( A S ( T ` B ) ) )

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
    cc
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
    cA
    cB
    cR
    co
    #
    cU
    cn0v
    cfv
    #
    cU
    cpv
    cfv
    #
    co
    #
    cT
    cfv
    #
    cA
    cB
    cT
    cfv
    #
    cS
    co
    #
    @9
    cT
    cfv
    #
    cW
    cpv
    cfv
    #
    co
    #
    @8
    cT
    cfv
    @14
    @7
    @3
    @4
    @5
    @9
    cX
    wcel
    #
    @12
    @17
    wceq
    @3
    @6
    simpl
    @3
    @4
    @5
    simprl
    #
    @3
    @4
    @5
    simprr
    #
    @7
    @0
    @18
    @0
    @1
    @2
    @6
    simpl1
    #
    cU
    cX
    @9
    lnomul.1
    @9
    eqid
    #
    nvzcl
    syl
    cA
    cB
    @9
    cR
    cS
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
    lnomul.1
    @23
    eqid
    #
    @10
    eqid
    #
    @16
    eqid
    #
    lnomul.5
    lnomul.6
    lnomul.7
    lnolin
    syl13anc
    @7
    @11
    @8
    cT
    @7
    @0
    @8
    cX
    wcel
    #
    @11
    @8
    wceq
    @21
    @7
    @0
    @4
    @5
    @27
    @21
    @19
    @20
    cA
    cB
    cR
    cU
    cX
    lnomul.1
    lnomul.5
    nvscl
    syl3anc
    @8
    cU
    @10
    cX
    @9
    lnomul.1
    @25
    @22
    nv0rid
    syl2anc
    fveq2d
    @7
    @17
    @14
    cW
    cn0v
    cfv
    #
    @16
    co
    #
    @14
    @3
    @17
    @29
    wceq
    @6
    @3
    @15
    @28
    @14
    @16
    @9
    cT
    cU
    cL
    cW
    cX
    @23
    @28
    lnomul.1
    @24
    @22
    @28
    eqid
    #
    lnomul.7
    lno0
    oveq2d
    adantr
    @7
    @1
    @14
    @23
    wcel
    #
    @29
    @14
    wceq
    @0
    @1
    @2
    @6
    simpl2
    #
    @7
    @1
    @4
    @13
    @23
    wcel
    @31
    @32
    @19
    @7
    cX
    @23
    cB
    cT
    @3
    cX
    @23
    cT
    wf
    @6
    cT
    cU
    cL
    cW
    cX
    @23
    lnomul.1
    @24
    lnomul.7
    lnof
    adantr
    @20
    ffvelrnd
    cA
    @13
    cS
    cW
    @23
    @24
    lnomul.6
    nvscl
    syl3anc
    @14
    cW
    @16
    @23
    @28
    @24
    @26
    @30
    nv0rid
    syl2anc
    eqtrd
    3eqtr3d
end
