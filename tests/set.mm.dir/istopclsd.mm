include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ccl.mm"
include "wceq.mm"
include "cv.mm"
include "cdif.mm"
include "cid.mm"
include "cin.mm"
include "cdm.mm"
include "cpw.mm"
include "crab.mm"
include "wa.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "adantr.mm"
include "wss.mm"
include "difss.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "fnelfp.mm"
include "syl2anc.mm"
include "bicomd.mm"
include "rabbidva.mm"
include "syl5eq.mm"
include "ccld.mm"
include "w3a.mm"
include "cun.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "sstrd.mm"
include "syl3anc.mm"
include "ssequn2.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "sylibr.mm"
include "ismrcd1.mm"
include "c0.mm"
include "0elpw.mm"
include "sylancl.mm"
include "mpbird.mm"
include "inss1.mm"
include "dmss.mm"
include "ax-mp.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "3ad2ant1.mm"
include "sseldd.mm"
include "elpwid.mm"
include "mpbid.mm"
include "uneq12d.mm"
include "eqtrd.mm"
include "unssd.mm"
include "vex.mm"
include "unex.mm"
include "elpw.mm"
include "eqid.mm"
include "mretopd.mm"
include "simpld.mm"
include "eqeltrd.mm"
include "cmrc.mm"
include "ctop.mm"
include "topontop.mm"
include "mrccls.mm"
include "simprd.mm"
include "eqtr4d.mm"
include "ismrcd2.mm"
include "jca.mm"

theorem istopclsd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cF: class F
  let cJ: class J
  let cV: class V
  assume istopclsd.b: |- ( ph -> B e. V )
  assume istopclsd.f: |- ( ph -> F : ~P B --> ~P B )
  assume istopclsd.e: |- ( ( ph /\ x C_ B ) -> x C_ ( F ` x ) )
  assume istopclsd.i: |- ( ( ph /\ x C_ B ) -> ( F ` ( F ` x ) ) = ( F ` x ) )
  assume istopclsd.z: |- ( ph -> ( F ` (/) ) = (/) )
  assume istopclsd.u: |- ( ( ph /\ x C_ B /\ y C_ B ) -> ( F ` ( x u. y ) ) = ( ( F ` x ) u. ( F ` y ) ) )
  assume istopclsd.j: |- J = { z e. ~P B | ( F ` ( B \ z ) ) = ( B \ z ) }

  disjoint B x
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint J x
  disjoint J y
  disjoint V x
  disjoint V y
  disjoint V z
  assert |- ( ph -> ( J e. ( TopOn ` B ) /\ ( cls ` J ) = F ) )

  proof
    wph
    cJ
    cB
    ctopon
    cfv
    #
    wcel
    #
    cJ
    ccl
    cfv
    #
    cF
    wceq
    wph
    cJ
    cB
    vz
    cv
    #
    cdif
    #
    cF
    cid
    cin
    #
    cdm
    #
    wcel
    #
    vz
    cB
    cpw
    #
    crab
    #
    @0
    wph
    cJ
    @4
    cF
    cfv
    @4
    wceq
    #
    vz
    @8
    crab
    @9
    istopclsd.j
    wph
    @10
    @7
    vz
    @8
    wph
    @3
    @8
    wcel
    #
    wa
    #
    @7
    @10
    @12
    cF
    @8
    wfn
    #
    @4
    @8
    wcel
    #
    @7
    @10
    wb
    wph
    @13
    @11
    wph
    @8
    @8
    cF
    wf
    #
    @13
    istopclsd.f
    @8
    @8
    cF
    ffn
    syl
    #
    adantr
    wph
    @14
    @11
    wph
    @14
    @4
    cB
    wss
    #
    cB
    @3
    difss
    wph
    cB
    cV
    wcel
    @14
    @17
    wb
    istopclsd.b
    @4
    cB
    cV
    elpw2g
    syl
    mpbiri
    adantr
    @8
    cF
    @4
    fnelfp
    syl2anc
    bicomd
    rabbidva
    syl5eq
    #
    wph
    @9
    @0
    wcel
    #
    @6
    @9
    ccld
    cfv
    #
    wceq
    #
    wph
    vx
    vy
    vz
    cB
    @9
    @6
    wph
    vx
    vy
    cB
    cF
    cV
    istopclsd.b
    istopclsd.f
    istopclsd.e
    wph
    vx
    cv
    #
    cB
    wss
    #
    vy
    cv
    #
    @22
    wss
    #
    w3a
    #
    @22
    cF
    cfv
    #
    @24
    cF
    cfv
    #
    cun
    #
    @27
    wceq
    @28
    @27
    wss
    @26
    @22
    @24
    cun
    #
    cF
    cfv
    #
    @29
    @27
    @26
    wph
    @23
    @24
    cB
    wss
    #
    @31
    @29
    wceq
    #
    wph
    @23
    @25
    simp1
    wph
    @23
    @25
    simp2
    #
    @26
    @24
    @22
    cB
    wph
    @23
    @25
    simp3
    @34
    sstrd
    istopclsd.u
    syl3anc
    @26
    @30
    @22
    cF
    @25
    wph
    @30
    @22
    wceq
    #
    @23
    @25
    @35
    @24
    @22
    ssequn2
    biimpi
    3ad2ant3
    fveq2d
    eqtr3d
    @28
    @27
    ssequn2
    sylibr
    #
    istopclsd.i
    ismrcd1
    wph
    c0
    @6
    wcel
    #
    c0
    cF
    cfv
    c0
    wceq
    #
    istopclsd.z
    wph
    @13
    c0
    @8
    wcel
    @37
    @38
    wb
    @16
    cB
    0elpw
    @8
    cF
    c0
    fnelfp
    sylancl
    mpbird
    wph
    @22
    @6
    wcel
    #
    @24
    @6
    wcel
    #
    w3a
    #
    @30
    @6
    wcel
    #
    @31
    @30
    wceq
    #
    @41
    @31
    @29
    @30
    @41
    wph
    @23
    @32
    @33
    wph
    @39
    @40
    simp1
    @41
    @22
    cB
    @41
    @6
    @8
    @22
    wph
    @39
    @6
    @8
    wss
    @40
    wph
    cF
    cdm
    #
    @6
    @8
    @5
    cF
    wss
    @6
    @44
    wss
    cF
    cid
    inss1
    @5
    cF
    dmss
    ax-mp
    wph
    @15
    @44
    @8
    wceq
    istopclsd.f
    @8
    @8
    cF
    fdm
    syl
    syl5sseq
    3ad2ant1
    #
    wph
    @39
    @40
    simp2
    #
    sseldd
    #
    elpwid
    #
    @41
    @24
    cB
    @41
    @6
    @8
    @24
    @45
    wph
    @39
    @40
    simp3
    #
    sseldd
    #
    elpwid
    #
    istopclsd.u
    syl3anc
    @41
    @27
    @22
    @28
    @24
    @41
    @39
    @27
    @22
    wceq
    #
    @46
    @41
    @13
    @22
    @8
    wcel
    @39
    @52
    wb
    wph
    @39
    @13
    @40
    @16
    3ad2ant1
    #
    @47
    @8
    cF
    @22
    fnelfp
    syl2anc
    mpbid
    @41
    @40
    @28
    @24
    wceq
    #
    @49
    @41
    @13
    @24
    @8
    wcel
    @40
    @54
    wb
    @53
    @50
    @8
    cF
    @24
    fnelfp
    syl2anc
    mpbid
    uneq12d
    eqtrd
    @41
    @13
    @30
    @8
    wcel
    #
    @42
    @43
    wb
    @53
    @41
    @30
    cB
    wss
    @55
    @41
    @22
    @24
    cB
    @48
    @51
    unssd
    @30
    cB
    @22
    @24
    vx
    vex
    vy
    vex
    unex
    elpw
    sylibr
    @8
    cF
    @30
    fnelfp
    syl2anc
    mpbird
    @9
    eqid
    mretopd
    #
    simpld
    eqeltrd
    #
    wph
    @2
    @6
    cmrc
    cfv
    #
    cF
    wph
    @2
    cJ
    ccld
    cfv
    #
    cmrc
    cfv
    #
    @58
    wph
    cJ
    ctop
    wcel
    #
    @2
    @60
    wceq
    wph
    @1
    @61
    @57
    cB
    cJ
    topontop
    syl
    @60
    cJ
    @60
    eqid
    mrccls
    syl
    wph
    @6
    @59
    cmrc
    wph
    @6
    @20
    @59
    wph
    @19
    @21
    @56
    simprd
    wph
    cJ
    @9
    ccld
    @18
    fveq2d
    eqtr4d
    fveq2d
    eqtr4d
    wph
    vx
    vy
    cB
    cF
    cV
    istopclsd.b
    istopclsd.f
    istopclsd.e
    @36
    istopclsd.i
    ismrcd2
    eqtr4d
    jca
end
