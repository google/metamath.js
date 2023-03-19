include "cin.mm"
include "wbr.mm"
include "wpss.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "co.mm"
include "clmod.mm"
include "wcel.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "lcvpss.mm"
include "lcvexchlem1.mm"
include "mpbid.mm"
include "w3a.mm"
include "csubg.mm"
include "cfv.mm"
include "3ad2ant1.mm"
include "lsssssubg.mm"
include "syl.mm"
include "simp2.mm"
include "sseldd.mm"
include "lsmub2.mm"
include "syl2anc.mm"
include "simp3r.mm"
include "lsmless1.mm"
include "cabl.mm"
include "lmodabl.mm"
include "lsmcom.mm"
include "sseqtr4d.mm"
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
include "mp2and.mm"
include "ineq1.mm"
include "simp3l.mm"
include "lcvexchlem2.mm"
include "eqeq1d.mm"
include "syl5ib.mm"
include "sseqin2.mm"
include "sylib.mm"
include "eqeq12d.mm"
include "orim12d.mm"
include "3exp.mm"
include "ralrimiv.mm"
include "lssincl.mm"
include "mpbir2and.mm"

theorem lcvexchlem4
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
  assume lcvexch.f: |- ( ph -> T C ( T .(+) U ) )


  assert |- ( ph -> ( T i^i U ) C U )

  proof
    wph
    cT
    cU
    cin
    #
    cU
    cC
    wbr
    @0
    cU
    wpss
    #
    @0
    vs
    cv
    #
    wss
    #
    @2
    cU
    wss
    #
    wa
    #
    @2
    @0
    wceq
    #
    @2
    cU
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
    cT
    cT
    cU
    c.po
    co
    #
    wpss
    #
    @1
    wph
    cC
    cS
    cT
    @10
    cW
    clmod
    lcvexch.s
    lcvexch.c
    lcvexch.w
    lcvexch.t
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
    c.po
    cS
    cT
    cU
    cW
    lcvexch.s
    lcvexch.p
    lsmcl
    syl3anc
    #
    lcvexch.f
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
    mpbid
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
    cT
    c.po
    co
    #
    cT
    wceq
    #
    @18
    @10
    wceq
    #
    wo
    #
    @8
    @17
    cT
    @18
    wss
    #
    @18
    @10
    wss
    #
    @21
    @17
    @2
    cW
    csubg
    cfv
    #
    wcel
    cT
    @24
    wcel
    #
    @22
    @17
    cS
    @24
    @2
    @17
    @12
    cS
    @24
    wss
    #
    wph
    @16
    @12
    @5
    lcvexch.w
    3ad2ant1
    #
    cS
    cW
    lcvexch.s
    lsssssubg
    #
    syl
    #
    wph
    @16
    @5
    simp2
    #
    sseldd
    @17
    cS
    @24
    cT
    @29
    wph
    @16
    @13
    @5
    lcvexch.t
    3ad2ant1
    #
    sseldd
    #
    c.po
    @2
    cT
    cW
    lcvexch.p
    lsmub2
    syl2anc
    @17
    @18
    cU
    cT
    c.po
    co
    #
    @10
    @17
    cU
    @24
    wcel
    #
    @25
    @4
    @18
    @33
    wss
    @17
    cS
    @24
    cU
    @29
    wph
    @16
    @14
    @5
    lcvexch.u
    3ad2ant1
    #
    sseldd
    #
    @32
    wph
    @16
    @3
    @4
    simp3r
    #
    c.po
    @2
    cU
    cT
    cW
    lcvexch.p
    lsmless1
    syl3anc
    wph
    @16
    @10
    @33
    wceq
    #
    @5
    wph
    cW
    cabl
    wcel
    #
    @25
    @34
    @38
    wph
    @12
    @39
    lcvexch.w
    cW
    lmodabl
    syl
    wph
    cS
    @24
    cT
    wph
    @12
    @26
    lcvexch.w
    @28
    syl
    #
    lcvexch.t
    sseldd
    wph
    cS
    @24
    cU
    @40
    lcvexch.u
    sseldd
    c.po
    cT
    cU
    cW
    lcvexch.p
    lsmcom
    syl3anc
    3ad2ant1
    sseqtr4d
    @17
    cT
    @10
    cC
    wbr
    #
    @22
    @23
    wa
    #
    @21
    wi
    #
    wph
    @16
    @41
    @5
    lcvexch.f
    3ad2ant1
    wph
    @16
    @41
    @43
    wi
    @5
    wph
    @16
    wa
    #
    @41
    @11
    cT
    vr
    cv
    #
    wss
    #
    @45
    @10
    wss
    #
    wa
    #
    @45
    cT
    wceq
    #
    @45
    @10
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
    @43
    wph
    @41
    @54
    wb
    @16
    wph
    cC
    cS
    cT
    @10
    cW
    clmod
    vr
    lcvexch.s
    lcvexch.c
    lcvexch.w
    lcvexch.t
    @15
    lcvbr3
    adantr
    @44
    @53
    @43
    @11
    @44
    @18
    cS
    wcel
    #
    @53
    @43
    wi
    @44
    @12
    @16
    @13
    @55
    wph
    @12
    @16
    lcvexch.w
    adantr
    wph
    @16
    simpr
    wph
    @13
    @16
    lcvexch.t
    adantr
    c.po
    cS
    @2
    cT
    cW
    lcvexch.s
    lcvexch.p
    lsmcl
    syl3anc
    @52
    @43
    vr
    @18
    cS
    @45
    @18
    wceq
    #
    @48
    @42
    @51
    @21
    @56
    @46
    @22
    @47
    @23
    @45
    @18
    cT
    sseq2
    @45
    @18
    @10
    sseq1
    anbi12d
    @56
    @49
    @19
    @50
    @20
    @45
    @18
    cT
    eqeq1
    @45
    @18
    @10
    eqeq1
    orbi12d
    imbi12d
    rspcv
    syl
    adantld
    sylbid
    3adant3
    mpd
    mp2and
    @17
    @19
    @6
    @20
    @7
    @19
    @18
    cU
    cin
    #
    @0
    wceq
    @17
    @6
    @18
    cT
    cU
    ineq1
    @17
    @57
    @2
    @0
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
    @27
    @31
    @35
    @30
    wph
    @16
    @3
    @4
    simp3l
    @37
    lcvexchlem2
    #
    eqeq1d
    syl5ib
    @20
    @57
    @10
    cU
    cin
    #
    wceq
    @17
    @7
    @18
    @10
    cU
    ineq1
    @17
    @57
    @2
    @59
    cU
    @58
    @17
    cU
    @10
    wss
    #
    @59
    cU
    wceq
    @17
    @25
    @34
    @60
    @32
    @36
    c.po
    cT
    cU
    cW
    lcvexch.p
    lsmub2
    syl2anc
    cU
    @10
    sseqin2
    sylib
    eqeq12d
    syl5ib
    orim12d
    mpd
    3exp
    ralrimiv
    wph
    cC
    cS
    @0
    cU
    cW
    clmod
    vs
    lcvexch.s
    lcvexch.c
    lcvexch.w
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
    cS
    cT
    cU
    cW
    lcvexch.s
    lssincl
    syl3anc
    lcvexch.u
    lcvbr3
    mpbir2and
end
