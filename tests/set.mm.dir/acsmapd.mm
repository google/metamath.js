include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "cvv.mm"
include "wrex.mm"
include "fvex.mm"
include "ssex.mm"
include "syl.mm"
include "sseld.mm"
include "acsficl2d.mm"
include "sylibd.mm"
include "ralrimiv.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "ac6sg.mm"
include "sylc.mm"
include "simprl.mm"
include "wi.mm"
include "wal.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "csn.mm"
include "cacs.mm"
include "ad2antrr.mm"
include "acsmred.mm"
include "wfn.mm"
include "simplrl.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "sylancom.mm"
include "snssd.mm"
include "unissd.mm"
include "frn.mm"
include "unifpw.mm"
include "syl6sseq.mm"
include "sstrd.mm"
include "mrcssd.mm"
include "simprr.mm"
include "r19.21bi.mm"
include "unisn.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "sseldd.mm"
include "ex.mm"
include "alrimi.mm"
include "dfss2.mm"
include "sylibr.mm"
include "jca.mm"
include "eximdv.mm"
include "mpd.mm"

theorem acsmapd
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume acsmapd.1: |- ( ph -> A e. ( ACS ` X ) )
  assume acsmapd.2: |- N = ( mrCls ` A )
  assume acsmapd.3: |- ( ph -> S C_ X )
  assume acsmapd.4: |- ( ph -> T C_ ( N ` S ) )

  disjoint T f
  disjoint f ph
  disjoint S f
  disjoint N f
  disjoint T x
  disjoint f x
  disjoint ph x
  disjoint S x
  disjoint S y
  disjoint f y
  disjoint x y
  disjoint N x
  disjoint N y
  assert |- ( ph -> E. f ( f : T --> ( ~P S i^i Fin ) /\ T C_ ( N ` U. ran f ) ) )

  proof
    wph
    cT
    cS
    cpw
    cfn
    cin
    #
    vf
    cv
    #
    wf
    #
    vx
    cv
    #
    @3
    @1
    cfv
    #
    cN
    cfv
    #
    wcel
    #
    vx
    cT
    wral
    #
    wa
    #
    vf
    wex
    #
    @2
    cT
    @1
    crn
    #
    cuni
    #
    cN
    cfv
    #
    wss
    #
    wa
    #
    vf
    wex
    wph
    cT
    cvv
    wcel
    #
    @3
    vy
    cv
    #
    cN
    cfv
    #
    wcel
    #
    vy
    @0
    wrex
    #
    vx
    cT
    wral
    @9
    wph
    cT
    cS
    cN
    cfv
    #
    wss
    @15
    acsmapd.4
    cT
    @20
    cS
    cN
    fvex
    ssex
    syl
    wph
    @19
    vx
    cT
    wph
    @3
    cT
    wcel
    #
    @3
    @20
    wcel
    @19
    wph
    cT
    @20
    @3
    acsmapd.4
    sseld
    wph
    vy
    cA
    cS
    cN
    cX
    @3
    acsmapd.1
    acsmapd.2
    acsmapd.3
    acsficl2d
    sylibd
    ralrimiv
    @18
    @6
    vx
    vy
    cT
    @0
    vf
    cvv
    @16
    @4
    wceq
    @17
    @5
    @3
    @16
    @4
    cN
    fveq2
    eleq2d
    ac6sg
    sylc
    wph
    @8
    @14
    vf
    wph
    @8
    @14
    wph
    @8
    wa
    #
    @2
    @13
    wph
    @2
    @7
    simprl
    @22
    @21
    @3
    @12
    wcel
    #
    wi
    #
    vx
    wal
    @13
    @22
    @24
    vx
    wph
    @8
    vx
    wph
    vx
    nfv
    @2
    @7
    vx
    @2
    vx
    nfv
    @6
    vx
    cT
    nfra1
    nfan
    nfan
    @22
    @21
    @23
    @22
    @21
    wa
    #
    @4
    csn
    #
    cuni
    #
    cN
    cfv
    #
    @12
    @3
    @25
    cA
    @27
    cN
    @11
    cX
    @25
    cA
    cX
    wph
    cA
    cX
    cacs
    cfv
    wcel
    @8
    @21
    acsmapd.1
    ad2antrr
    acsmred
    acsmapd.2
    @25
    @26
    @10
    @25
    @4
    @10
    @22
    @21
    @1
    cT
    wfn
    #
    @4
    @10
    wcel
    @25
    @2
    @29
    wph
    @2
    @7
    @21
    simplrl
    #
    cT
    @0
    @1
    ffn
    syl
    cT
    @3
    @1
    fnfvelrn
    sylancom
    snssd
    unissd
    @25
    @11
    cS
    cX
    @25
    @2
    @11
    cS
    wss
    @30
    @2
    @11
    @0
    cuni
    cS
    @2
    @10
    @0
    cT
    @0
    @1
    frn
    unissd
    cS
    unifpw
    syl6sseq
    syl
    wph
    cS
    cX
    wss
    @8
    @21
    acsmapd.3
    ad2antrr
    sstrd
    mrcssd
    @25
    @3
    @5
    @28
    @22
    @6
    vx
    cT
    wph
    @2
    @7
    simprr
    r19.21bi
    @27
    @4
    cN
    @4
    @3
    @1
    fvex
    unisn
    fveq2i
    syl6eleqr
    sseldd
    ex
    alrimi
    vx
    cT
    @12
    dfss2
    sylibr
    jca
    ex
    eximdv
    mpd
end
