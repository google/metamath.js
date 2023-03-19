include "co.mm"
include "wbr.mm"
include "wpss.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "cin.mm"
include "clmod.mm"
include "wcel.mm"
include "lssincl.mm"
include "syl3anc.mm"
include "lcvpss.mm"
include "lcvexchlem1.mm"
include "mpbird.mm"
include "w3a.mm"
include "simp3l.mm"
include "ssrin.mm"
include "syl.mm"
include "inss2.mm"
include "jctir.mm"
include "3ad2ant1.mm"
include "wb.mm"
include "lcvbr3.mm"
include "adantr.mm"
include "simpr.mm"
include "sseq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "adantld.mm"
include "sylbid.mm"
include "3adant3.mm"
include "mpd.mm"
include "oveq1.mm"
include "simp2.mm"
include "simp3r.mm"
include "lcvexchlem3.mm"
include "csubg.mm"
include "cfv.mm"
include "lsssssubg.mm"
include "sseldd.mm"
include "inss1.mm"
include "a1i.mm"
include "lsmss1.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "cabl.mm"
include "lmodabl.mm"
include "lsmcom.mm"
include "orim12d.mm"
include "3exp.mm"
include "ralrimiv.mm"
include "lsmcl.mm"
include "mpbir2and.mm"

theorem lcvexchlem5
  let wph: wff ph
  let cC: class C
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cW: class W
  let vr: setvar r
  let vs: setvar s
  assume lcvexch.s: |- S = ( LSubSp ` W )
  assume lcvexch.p: |- .(+) = ( LSSum ` W )
  assume lcvexch.c: |- C = ( <oL ` W )
  assume lcvexch.w: |- ( ph -> W e. LMod )
  assume lcvexch.t: |- ( ph -> T e. S )
  assume lcvexch.u: |- ( ph -> U e. S )
  assume lcvexch.g: |- ( ph -> ( T i^i U ) C U )


  assert |- ( ph -> T C ( T .(+) U ) )

  proof
    wph
    cT
    cT
    cU
    c.po
    co
    #
    cC
    wbr
    cT
    @0
    wpss
    #
    cT
    vs
    cv
    #
    wss
    #
    @2
    @0
    wss
    #
    wa
    #
    @2
    cT
    wceq
    #
    @2
    @0
    wceq
    #
    wo
    #
    wi
    #
    vs
    cS
    wral
    wph
    @1
    cT
    cU
    cin
    #
    cU
    wpss
    #
    wph
    cC
    cS
    @10
    cU
    cW
    clmod
    lcvexch.s
    lcvexch.c
    lcvexch.w
    wph
    cW
    clmod
    wcel
    #
    cT
    cS
    wcel
    #
    cU
    cS
    wcel
    #
    @10
    cS
    wcel
    lcvexch.w
    lcvexch.t
    lcvexch.u
    cS
    cT
    cU
    cW
    lcvexch.s
    lssincl
    syl3anc
    #
    lcvexch.u
    lcvexch.g
    lcvpss
    wph
    cC
    c.po
    cS
    cT
    cU
    cW
    lcvexch.s
    lcvexch.p
    lcvexch.c
    lcvexch.w
    lcvexch.t
    lcvexch.u
    lcvexchlem1
    mpbird
    wph
    @9
    vs
    cS
    wph
    @2
    cS
    wcel
    #
    @5
    @8
    wph
    @16
    @5
    w3a
    #
    @2
    cU
    cin
    #
    @10
    wceq
    #
    @18
    cU
    wceq
    #
    wo
    #
    @8
    @17
    @10
    @18
    wss
    #
    @18
    cU
    wss
    #
    wa
    #
    @21
    @17
    @22
    @23
    @17
    @3
    @22
    wph
    @16
    @3
    @4
    simp3l
    #
    cT
    @2
    cU
    ssrin
    syl
    @2
    cU
    inss2
    jctir
    @17
    @10
    cU
    cC
    wbr
    #
    @24
    @21
    wi
    #
    wph
    @16
    @26
    @5
    lcvexch.g
    3ad2ant1
    wph
    @16
    @26
    @27
    wi
    @5
    wph
    @16
    wa
    #
    @26
    @11
    @10
    vr
    cv
    #
    wss
    #
    @29
    cU
    wss
    #
    wa
    #
    @29
    @10
    wceq
    #
    @29
    cU
    wceq
    #
    wo
    #
    wi
    #
    vr
    cS
    wral
    #
    wa
    #
    @27
    wph
    @26
    @38
    wb
    @16
    wph
    cC
    cS
    @10
    cU
    cW
    clmod
    vr
    lcvexch.s
    lcvexch.c
    lcvexch.w
    @15
    lcvexch.u
    lcvbr3
    adantr
    @28
    @37
    @27
    @11
    @28
    @18
    cS
    wcel
    #
    @37
    @27
    wi
    @28
    @12
    @16
    @14
    @39
    wph
    @12
    @16
    lcvexch.w
    adantr
    wph
    @16
    simpr
    wph
    @14
    @16
    lcvexch.u
    adantr
    cS
    @2
    cU
    cW
    lcvexch.s
    lssincl
    syl3anc
    @36
    @27
    vr
    @18
    cS
    @29
    @18
    wceq
    #
    @32
    @24
    @35
    @21
    @40
    @30
    @22
    @31
    @23
    @29
    @18
    @10
    sseq2
    @29
    @18
    cU
    sseq1
    anbi12d
    @40
    @33
    @19
    @34
    @20
    @29
    @18
    @10
    eqeq1
    @29
    @18
    cU
    eqeq1
    orbi12d
    imbi12d
    rspcv
    syl
    adantld
    sylbid
    3adant3
    mpd
    mpd
    @17
    @19
    @6
    @20
    @7
    @19
    @18
    cT
    c.po
    co
    #
    @10
    cT
    c.po
    co
    #
    wceq
    @17
    @6
    @18
    @10
    cT
    c.po
    oveq1
    @17
    @41
    @2
    @42
    cT
    @17
    cC
    c.po
    @2
    cS
    cT
    cU
    cW
    lcvexch.s
    lcvexch.p
    lcvexch.c
    wph
    @16
    @12
    @5
    lcvexch.w
    3ad2ant1
    wph
    @16
    @13
    @5
    lcvexch.t
    3ad2ant1
    wph
    @16
    @14
    @5
    lcvexch.u
    3ad2ant1
    wph
    @16
    @5
    simp2
    @25
    wph
    @16
    @3
    @4
    simp3r
    lcvexchlem3
    #
    wph
    @16
    @42
    cT
    wceq
    #
    @5
    wph
    @10
    cW
    csubg
    cfv
    #
    wcel
    cT
    @45
    wcel
    #
    @10
    cT
    wss
    #
    @44
    wph
    cS
    @45
    @10
    wph
    @12
    cS
    @45
    wss
    lcvexch.w
    cS
    cW
    lcvexch.s
    lsssssubg
    syl
    #
    @15
    sseldd
    wph
    cS
    @45
    cT
    @48
    lcvexch.t
    sseldd
    #
    @47
    wph
    cT
    cU
    inss1
    a1i
    c.po
    @10
    cT
    cW
    lcvexch.p
    lsmss1
    syl3anc
    3ad2ant1
    eqeq12d
    syl5ib
    @20
    @41
    cU
    cT
    c.po
    co
    #
    wceq
    @17
    @7
    @18
    cU
    cT
    c.po
    oveq1
    @17
    @41
    @2
    @50
    @0
    @43
    wph
    @16
    @50
    @0
    wceq
    #
    @5
    wph
    cW
    cabl
    wcel
    #
    cU
    @45
    wcel
    @46
    @51
    wph
    @12
    @52
    lcvexch.w
    cW
    lmodabl
    syl
    wph
    cS
    @45
    cU
    @48
    lcvexch.u
    sseldd
    @49
    c.po
    cU
    cT
    cW
    lcvexch.p
    lsmcom
    syl3anc
    3ad2ant1
    eqeq12d
    syl5ib
    orim12d
    mpd
    3exp
    ralrimiv
    wph
    cC
    cS
    cT
    @0
    cW
    clmod
    vs
    lcvexch.s
    lcvexch.c
    lcvexch.w
    lcvexch.t
    wph
    @12
    @13
    @14
    @0
    cS
    wcel
    lcvexch.w
    lcvexch.t
    lcvexch.u
    c.po
    cS
    cT
    cU
    cW
    lcvexch.s
    lcvexch.p
    lsmcl
    syl3anc
    lcvbr3
    mpbir2and
end
