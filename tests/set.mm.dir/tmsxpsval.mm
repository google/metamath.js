include "cop.mm"
include "co.mm"
include "ctmt.mm"
include "cfv.mm"
include "cds.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cpr.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cxps.mm"
include "cxme.mm"
include "eqid.mm"
include "cxmt.mm"
include "wcel.mm"
include "tmsxms.mm"
include "syl.mm"
include "wss.mm"
include "wceq.mm"
include "tmsds.mm"
include "tmsbas.mm"
include "fveq2d.mm"
include "3eltr3d.mm"
include "ssid.mm"
include "xmetres2.mm"
include "sylancl.mm"
include "eleqtrd.mm"
include "xpsdsval.mm"
include "ovresd.mm"
include "oveqd.mm"
include "eqtr4d.mm"
include "preq12d.mm"
include "supeq1d.mm"
include "eqtrd.mm"

theorem tmsxpsval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  assume tmsxps.p: |- P = ( dist ` ( ( toMetSp ` M ) Xs. ( toMetSp ` N ) ) )
  assume tmsxps.1: |- ( ph -> M e. ( *Met ` X ) )
  assume tmsxps.2: |- ( ph -> N e. ( *Met ` Y ) )
  assume tmsxpsval.a: |- ( ph -> A e. X )
  assume tmsxpsval.b: |- ( ph -> B e. Y )
  assume tmsxpsval.c: |- ( ph -> C e. X )
  assume tmsxpsval.d: |- ( ph -> D e. Y )


  assert |- ( ph -> ( <. A , B >. P <. C , D >. ) = sup ( { ( A M C ) , ( B N D ) } , RR* , < ) )

  proof
    wph
    cA
    cB
    cop
    cC
    cD
    cop
    cP
    co
    cA
    cC
    cM
    ctmt
    cfv
    #
    cds
    cfv
    #
    @0
    cbs
    cfv
    #
    @2
    cxp
    cres
    #
    co
    #
    cB
    cD
    cN
    ctmt
    cfv
    #
    cds
    cfv
    #
    @5
    cbs
    cfv
    #
    @7
    cxp
    cres
    #
    co
    #
    cpr
    #
    cxr
    clt
    csup
    cA
    cC
    cM
    co
    #
    cB
    cD
    cN
    co
    #
    cpr
    #
    cxr
    clt
    csup
    wph
    cA
    cB
    cC
    cD
    cP
    @0
    @5
    @0
    @5
    cxps
    co
    #
    @3
    @8
    cxme
    cxme
    @2
    @7
    @14
    eqid
    @2
    eqid
    @7
    eqid
    wph
    cM
    cX
    cxmt
    cfv
    #
    wcel
    #
    @0
    cxme
    wcel
    tmsxps.1
    cM
    @0
    cX
    @0
    eqid
    #
    tmsxms
    syl
    wph
    cN
    cY
    cxmt
    cfv
    #
    wcel
    #
    @5
    cxme
    wcel
    tmsxps.2
    cN
    @5
    cY
    @5
    eqid
    #
    tmsxms
    syl
    tmsxps.p
    @3
    eqid
    @8
    eqid
    wph
    @1
    @2
    cxmt
    cfv
    #
    wcel
    @2
    @2
    wss
    @3
    @21
    wcel
    wph
    cM
    @15
    @1
    @21
    tmsxps.1
    wph
    @16
    cM
    @1
    wceq
    tmsxps.1
    cM
    @0
    cX
    @17
    tmsds
    syl
    #
    wph
    cX
    @2
    cxmt
    wph
    @16
    cX
    @2
    wceq
    tmsxps.1
    cM
    @0
    cX
    @17
    tmsbas
    syl
    #
    fveq2d
    3eltr3d
    @2
    ssid
    @1
    @2
    @2
    xmetres2
    sylancl
    wph
    @6
    @7
    cxmt
    cfv
    #
    wcel
    @7
    @7
    wss
    @8
    @24
    wcel
    wph
    cN
    @18
    @6
    @24
    tmsxps.2
    wph
    @19
    cN
    @6
    wceq
    tmsxps.2
    cN
    @5
    cY
    @20
    tmsds
    syl
    #
    wph
    cY
    @7
    cxmt
    wph
    @19
    cY
    @7
    wceq
    tmsxps.2
    cN
    @5
    cY
    @20
    tmsbas
    syl
    #
    fveq2d
    3eltr3d
    @7
    ssid
    @6
    @7
    @7
    xmetres2
    sylancl
    wph
    cA
    cX
    @2
    tmsxpsval.a
    @23
    eleqtrd
    #
    wph
    cB
    cY
    @7
    tmsxpsval.b
    @26
    eleqtrd
    #
    wph
    cC
    cX
    @2
    tmsxpsval.c
    @23
    eleqtrd
    #
    wph
    cD
    cY
    @7
    tmsxpsval.d
    @26
    eleqtrd
    #
    xpsdsval
    wph
    cxr
    @10
    @13
    clt
    wph
    @4
    @11
    @9
    @12
    wph
    @4
    cA
    cC
    @1
    co
    @11
    wph
    cA
    cC
    @1
    @2
    @27
    @29
    ovresd
    wph
    cM
    @1
    cA
    cC
    @22
    oveqd
    eqtr4d
    wph
    @9
    cB
    cD
    @6
    co
    @12
    wph
    cB
    cD
    @6
    @7
    @28
    @30
    ovresd
    wph
    cN
    @6
    cB
    cD
    @25
    oveqd
    eqtr4d
    preq12d
    supeq1d
    eqtrd
end
