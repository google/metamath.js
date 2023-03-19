include "cv.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cort.mm"
include "cfv.mm"
include "wrex.mm"
include "cpjh.mm"
include "cph.mm"
include "wcel.mm"
include "csh.mm"
include "wb.mm"
include "cch.mm"
include "chsh.mm"
include "syl.mm"
include "shocsh.mm"
include "shsel.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "wa.mm"
include "simprr.mm"
include "simprll.mm"
include "simprlr.mm"
include "rspe.mm"
include "pjpreeq.mm"
include "adantr.mm"
include "mpbir2and.mm"
include "wss.mm"
include "shococss.mm"
include "sseldd.mm"
include "chil.mm"
include "shel.mm"
include "ax-hvcom.mm"
include "eqtrd.mm"
include "choccl.mm"
include "shless.mm"
include "syl31anc.mm"
include "shscom.mm"
include "sseqtr4d.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "exp32.mm"
include "rexlimdvv.mm"
include "mpd.mm"

theorem pjpjpre
  let wph: wff ph
  let cA: class A
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjpjpre.1: |- ( ph -> H e. CH )
  assume pjpjpre.2: |- ( ph -> A e. ( H +H ( _|_ ` H ) ) )


  assert |- ( ph -> A = ( ( ( projh ` H ) ` A ) +h ( ( projh ` ( _|_ ` H ) ) ` A ) ) )

  proof
    wph
    cA
    vx
    cv
    #
    vy
    cv
    #
    cva
    co
    #
    wceq
    #
    vy
    cH
    cort
    cfv
    #
    wrex
    #
    vx
    cH
    wrex
    #
    cA
    cA
    cH
    cpjh
    cfv
    cfv
    #
    cA
    @4
    cpjh
    cfv
    cfv
    #
    cva
    co
    #
    wceq
    #
    wph
    cA
    cH
    @4
    cph
    co
    #
    wcel
    #
    @6
    pjpjpre.2
    wph
    cH
    csh
    wcel
    #
    @4
    csh
    wcel
    #
    @12
    @6
    wb
    wph
    cH
    cch
    wcel
    #
    @13
    pjpjpre.1
    cH
    chsh
    #
    syl
    #
    wph
    @13
    @14
    @17
    cH
    shocsh
    #
    syl
    #
    vx
    vy
    cH
    @4
    cA
    shsel
    syl2anc
    mpbid
    wph
    @3
    @10
    vx
    vy
    cH
    @4
    wph
    @0
    cH
    wcel
    #
    @1
    @4
    wcel
    #
    wa
    #
    @3
    @10
    wph
    @22
    @3
    wa
    #
    wa
    #
    cA
    @2
    @9
    wph
    @22
    @3
    simprr
    #
    @24
    @7
    @0
    @8
    @1
    cva
    @24
    @7
    @0
    wceq
    #
    @20
    @5
    wph
    @20
    @21
    @3
    simprll
    #
    @24
    @21
    @3
    @5
    wph
    @20
    @21
    @3
    simprlr
    #
    @25
    @3
    vy
    @4
    rspe
    syl2anc
    wph
    @26
    @20
    @5
    wa
    wb
    #
    @23
    wph
    @15
    @12
    @29
    pjpjpre.1
    pjpjpre.2
    vy
    cA
    @0
    cH
    pjpreeq
    syl2anc
    adantr
    mpbir2and
    @24
    @8
    @1
    wceq
    #
    @21
    cA
    @1
    @0
    cva
    co
    #
    wceq
    #
    vx
    @4
    cort
    cfv
    #
    wrex
    #
    @28
    @24
    @0
    @33
    wcel
    @32
    @34
    @24
    cH
    @33
    @0
    wph
    cH
    @33
    wss
    #
    @23
    wph
    @13
    @35
    @17
    cH
    shococss
    syl
    #
    adantr
    @27
    sseldd
    @24
    cA
    @2
    @31
    @25
    @24
    @0
    chil
    wcel
    #
    @1
    chil
    wcel
    #
    @2
    @31
    wceq
    @24
    @13
    @20
    @37
    @24
    @15
    @13
    wph
    @15
    @23
    pjpjpre.1
    adantr
    @16
    syl
    #
    @27
    @0
    cH
    shel
    syl2anc
    @24
    @14
    @21
    @38
    @24
    @13
    @14
    @39
    @18
    syl
    @28
    @1
    @4
    shel
    syl2anc
    @0
    @1
    ax-hvcom
    syl2anc
    eqtrd
    @32
    vx
    @33
    rspe
    syl2anc
    wph
    @30
    @21
    @34
    wa
    wb
    #
    @23
    wph
    @4
    cch
    wcel
    #
    cA
    @4
    @33
    cph
    co
    #
    wcel
    @40
    wph
    @15
    @41
    pjpjpre.1
    cH
    choccl
    syl
    wph
    @11
    @42
    cA
    wph
    @11
    @33
    @4
    cph
    co
    #
    @42
    wph
    @13
    @33
    csh
    wcel
    #
    @14
    @35
    @11
    @43
    wss
    @17
    wph
    @14
    @44
    @19
    @4
    shocsh
    syl
    #
    @19
    @36
    cH
    @33
    @4
    shless
    syl31anc
    wph
    @14
    @44
    @42
    @43
    wceq
    @19
    @45
    @4
    @33
    shscom
    syl2anc
    sseqtr4d
    pjpjpre.2
    sseldd
    vx
    cA
    @1
    @4
    pjpreeq
    syl2anc
    adantr
    mpbir2and
    oveq12d
    eqtr4d
    exp32
    rexlimdvv
    mpd
end
