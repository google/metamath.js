include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "c1.mm"
include "cns.mm"
include "cfv.mm"
include "co.mm"
include "cc.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "cba.mm"
include "eqid.mm"
include "lnolin.mm"
include "mp3anr1.mm"
include "simp1.mm"
include "simpl.mm"
include "nvsid.mm"
include "syl2an.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "simpl2.mm"
include "wf.mm"
include "lnof.mm"
include "ffvelrn.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"

theorem lnoadd
  let cA: class A
  let cB: class B
  let cT: class T
  let cU: class U
  let cG: class G
  let cH: class H
  let cL: class L
  let cW: class W
  let cX: class X
  assume lnoadd.1: |- X = ( BaseSet ` U )
  assume lnoadd.5: |- G = ( +v ` U )
  assume lnoadd.6: |- H = ( +v ` W )
  assume lnoadd.7: |- L = ( U LnOp W )


  assert |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) /\ ( A e. X /\ B e. X ) ) -> ( T ` ( A G B ) ) = ( ( T ` A ) H ( T ` B ) ) )

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
    cA
    cU
    cns
    cfv
    #
    co
    #
    cB
    cG
    co
    #
    cT
    cfv
    #
    c1
    cA
    cT
    cfv
    #
    cW
    cns
    cfv
    #
    co
    #
    cB
    cT
    cfv
    #
    cH
    co
    #
    cA
    cB
    cG
    co
    #
    cT
    cfv
    @12
    @15
    cH
    co
    @3
    c1
    cc
    wcel
    @4
    @5
    @11
    @16
    wceq
    ax-1cn
    c1
    cA
    cB
    @8
    @13
    cT
    cU
    cG
    cH
    cL
    cW
    cX
    cW
    cba
    cfv
    #
    lnoadd.1
    @18
    eqid
    #
    lnoadd.5
    lnoadd.6
    @8
    eqid
    #
    @13
    eqid
    #
    lnoadd.7
    lnolin
    mp3anr1
    @7
    @10
    @17
    cT
    @7
    @9
    cA
    cB
    cG
    @3
    @0
    @4
    @9
    cA
    wceq
    @6
    @0
    @1
    @2
    simp1
    @4
    @5
    simpl
    #
    cA
    @8
    cU
    cX
    lnoadd.1
    @20
    nvsid
    syl2an
    oveq1d
    fveq2d
    @7
    @14
    @12
    @15
    cH
    @7
    @1
    @12
    @18
    wcel
    #
    @14
    @12
    wceq
    @0
    @1
    @2
    @6
    simpl2
    @3
    cX
    @18
    cT
    wf
    @4
    @23
    @6
    cT
    cU
    cL
    cW
    cX
    @18
    lnoadd.1
    @19
    lnoadd.7
    lnof
    @22
    cX
    @18
    cA
    cT
    ffvelrn
    syl2an
    @12
    @13
    cW
    @18
    @19
    @21
    nvsid
    syl2anc
    oveq1d
    3eqtr3d
end
