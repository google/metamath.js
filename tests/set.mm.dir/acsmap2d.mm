include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "wf.mm"
include "crn.mm"
include "cuni.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "wex.mm"
include "wceq.mm"
include "acsmred.mm"
include "mrissd.mm"
include "mrcssidd.mm"
include "sseqtr4d.mm"
include "acsmapd.mm"
include "simprl.mm"
include "cmre.mm"
include "wcel.mm"
include "adantr.mm"
include "simprr.mm"
include "mrcssvd.mm"
include "mrcssd.mm"
include "frn.mm"
include "unissd.mm"
include "unifpw.mm"
include "syl6sseq.mm"
include "ad2antrl.mm"
include "sstrd.mm"
include "mrcidmd.mm"
include "sseqtrd.mm"
include "eqsstrd.mm"
include "mrissmrcd.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"

theorem acsmap2d
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cI: class I
  let cN: class N
  let cX: class X
  assume acsmap2d.1: |- ( ph -> A e. ( ACS ` X ) )
  assume acsmap2d.2: |- N = ( mrCls ` A )
  assume acsmap2d.3: |- I = ( mrInd ` A )
  assume acsmap2d.4: |- ( ph -> S e. I )
  assume acsmap2d.5: |- ( ph -> T C_ X )
  assume acsmap2d.6: |- ( ph -> ( N ` S ) = ( N ` T ) )

  disjoint S f
  disjoint T f
  disjoint f ph
  disjoint N f
  assert |- ( ph -> E. f ( f : T --> ( ~P S i^i Fin ) /\ S = U. ran f ) )

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
    @2
    cS
    @4
    wceq
    #
    wa
    #
    vf
    wex
    wph
    cA
    cS
    cT
    vf
    cN
    cX
    acsmap2d.1
    acsmap2d.2
    wph
    cA
    cS
    cI
    cX
    acsmap2d.3
    wph
    cA
    cX
    acsmap2d.1
    acsmred
    #
    acsmap2d.4
    mrissd
    wph
    cT
    cT
    cN
    cfv
    #
    cS
    cN
    cfv
    #
    wph
    cA
    cT
    cN
    cX
    @10
    acsmap2d.2
    acsmap2d.5
    mrcssidd
    acsmap2d.6
    sseqtr4d
    acsmapd
    wph
    @7
    @9
    vf
    wph
    @7
    @9
    wph
    @7
    wa
    #
    @2
    @8
    wph
    @2
    @6
    simprl
    @13
    cA
    cS
    @4
    cI
    cN
    cX
    wph
    cA
    cX
    cmre
    cfv
    wcel
    @7
    @10
    adantr
    #
    acsmap2d.2
    acsmap2d.3
    @13
    cS
    @12
    @5
    @13
    cA
    cS
    cN
    cX
    @14
    acsmap2d.2
    @13
    cA
    cS
    cI
    cX
    acsmap2d.3
    @14
    wph
    cS
    cI
    wcel
    @7
    acsmap2d.4
    adantr
    #
    mrissd
    #
    mrcssidd
    @13
    @12
    @11
    @5
    wph
    @12
    @11
    wceq
    @7
    acsmap2d.6
    adantr
    @13
    @11
    @5
    cN
    cfv
    @5
    @13
    cA
    cT
    cN
    @5
    cX
    @14
    acsmap2d.2
    wph
    @2
    @6
    simprr
    @13
    cA
    @4
    cN
    cX
    @14
    acsmap2d.2
    mrcssvd
    mrcssd
    @13
    cA
    @4
    cN
    cX
    @14
    acsmap2d.2
    @13
    @4
    cS
    cX
    @2
    @4
    cS
    wss
    wph
    @6
    @2
    @4
    @0
    cuni
    cS
    @2
    @3
    @0
    cT
    @0
    @1
    frn
    unissd
    cS
    unifpw
    syl6sseq
    ad2antrl
    #
    @16
    sstrd
    mrcidmd
    sseqtrd
    eqsstrd
    sstrd
    @17
    @15
    mrissmrcd
    jca
    ex
    eximdv
    mpd
end
