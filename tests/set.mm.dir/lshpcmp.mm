include "wss.mm"
include "wceq.mm"
include "wpss.mm"
include "wn.mm"
include "cbs.mm"
include "cfv.mm"
include "wne.mm"
include "eqid.mm"
include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lshpne.mm"
include "clss.mm"
include "lshplss.mm"
include "lssss.mm"
include "cv.mm"
include "csn.mm"
include "clspn.mm"
include "clsm.mm"
include "co.mm"
include "wrex.mm"
include "wi.mm"
include "w3a.mm"
include "islshpsm.mm"
include "mpbid.mm"
include "simp3d.mm"
include "wa.mm"
include "id.mm"
include "adantrr.mm"
include "adantr.mm"
include "simpr.mm"
include "lsmcv.mm"
include "syl3an1.mm"
include "3expia.mm"
include "simplrr.mm"
include "sseq2d.mm"
include "eqeq2d.mm"
include "3imtr3d.mm"
include "exp42.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "mpid.mm"
include "necon3ad.mm"
include "df-pss.mm"
include "simplbi2.mm"
include "necon1bd.mm"
include "syl5com.mm"
include "eqimss.mm"
include "impbid1.mm"

theorem lshpcmp
  let wph: wff ph
  let cT: class T
  let cU: class U
  let cH: class H
  let cW: class W
  let vv: setvar v
  assume lshpcmp.h: |- H = ( LSHyp ` W )
  assume lshpcmp.w: |- ( ph -> W e. LVec )
  assume lshpcmp.t: |- ( ph -> T e. H )
  assume lshpcmp.u: |- ( ph -> U e. H )


  assert |- ( ph -> ( T C_ U <-> T = U ) )

  proof
    wph
    cT
    cU
    wss
    #
    cT
    cU
    wceq
    #
    wph
    cT
    cU
    wpss
    #
    wn
    #
    @0
    @1
    wph
    cU
    cW
    cbs
    cfv
    #
    wne
    @3
    wph
    cU
    cH
    @4
    cW
    @4
    eqid
    #
    lshpcmp.h
    wph
    cW
    clvec
    wcel
    #
    cW
    clmod
    wcel
    lshpcmp.w
    cW
    lveclmod
    syl
    #
    lshpcmp.u
    lshpne
    wph
    @2
    cU
    @4
    wph
    @2
    cU
    @4
    wss
    #
    cU
    @4
    wceq
    #
    wph
    cU
    cW
    clss
    cfv
    #
    wcel
    #
    @8
    wph
    @10
    cU
    cH
    cW
    @10
    eqid
    #
    lshpcmp.h
    @7
    lshpcmp.u
    lshplss
    #
    @10
    cU
    @4
    cW
    @5
    @12
    lssss
    syl
    wph
    cT
    vv
    cv
    #
    csn
    cW
    clspn
    cfv
    #
    cfv
    cW
    clsm
    cfv
    #
    co
    #
    @4
    wceq
    #
    vv
    @4
    wrex
    #
    @2
    @8
    @9
    wi
    #
    wi
    #
    wph
    cT
    @10
    wcel
    #
    cT
    @4
    wne
    #
    @19
    wph
    cT
    cH
    wcel
    @22
    @23
    @19
    w3a
    lshpcmp.t
    wph
    vv
    @16
    @10
    cT
    cH
    @15
    @4
    cW
    @5
    @15
    eqid
    #
    @12
    @16
    eqid
    #
    lshpcmp.h
    @7
    islshpsm
    mpbid
    simp3d
    wph
    @18
    @21
    vv
    @4
    wph
    @14
    @4
    wcel
    #
    @18
    @2
    @20
    wph
    @26
    @18
    wa
    wa
    #
    @2
    wa
    #
    cU
    @17
    wss
    #
    cU
    @17
    wceq
    #
    @8
    @9
    @27
    @2
    @29
    @30
    @27
    wph
    @26
    wa
    #
    @2
    @29
    @30
    wph
    @26
    @31
    @18
    @31
    id
    adantrr
    @31
    @16
    @10
    cT
    cU
    @15
    @4
    cW
    @14
    @5
    @12
    @24
    @25
    wph
    @6
    @26
    lshpcmp.w
    adantr
    wph
    @22
    @26
    wph
    @10
    cT
    cH
    cW
    @12
    lshpcmp.h
    @7
    lshpcmp.t
    lshplss
    adantr
    wph
    @11
    @26
    @13
    adantr
    wph
    @26
    simpr
    lsmcv
    syl3an1
    3expia
    @28
    @17
    @4
    cU
    wph
    @26
    @18
    @2
    simplrr
    #
    sseq2d
    @28
    @17
    @4
    cU
    @32
    eqeq2d
    3imtr3d
    exp42
    rexlimdv
    mpd
    mpid
    necon3ad
    mpd
    @0
    @2
    cT
    cU
    @2
    @0
    cT
    cU
    wne
    cT
    cU
    df-pss
    simplbi2
    necon1bd
    syl5com
    cT
    cU
    eqimss
    impbid1
end
