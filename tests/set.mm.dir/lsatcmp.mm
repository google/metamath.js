include "cv.mm"
include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "c0g.mm"
include "cdif.mm"
include "wrex.mm"
include "wss.mm"
include "wb.mm"
include "wcel.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "eqid.mm"
include "islsat.mm"
include "mpbid.mm"
include "wi.mm"
include "wne.mm"
include "wa.mm"
include "eldifsn.mm"
include "lsatn0.mm"
include "ad2antrr.mm"
include "clss.mm"
include "wo.mm"
include "lsatlssel.mm"
include "simplrl.mm"
include "simpr.mm"
include "lspsnat.mm"
include "syl31anc.mm"
include "ord.mm"
include "necon1ad.mm"
include "mpd.mm"
include "ex.mm"
include "eqimss.mm"
include "impbid1.mm"
include "syl5bi.mm"
include "sseq2.mm"
include "eqeq2.mm"
include "bibi12d.mm"
include "biimprcd.mm"
include "syl6.mm"
include "rexlimdv.mm"

theorem lsatcmp
  let wph: wff ph
  let cA: class A
  let cT: class T
  let cU: class U
  let cW: class W
  let vv: setvar v
  assume lsatcmp.a: |- A = ( LSAtoms ` W )
  assume lsatcmp.w: |- ( ph -> W e. LVec )
  assume lsatcmp.t: |- ( ph -> T e. A )
  assume lsatcmp.u: |- ( ph -> U e. A )


  assert |- ( ph -> ( T C_ U <-> T = U ) )

  proof
    wph
    cU
    vv
    cv
    #
    csn
    cW
    clspn
    cfv
    #
    cfv
    #
    wceq
    #
    vv
    cW
    cbs
    cfv
    #
    cW
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wrex
    #
    cT
    cU
    wss
    #
    cT
    cU
    wceq
    #
    wb
    #
    wph
    cU
    cA
    wcel
    #
    @8
    lsatcmp.u
    wph
    cW
    clmod
    wcel
    #
    @12
    @8
    wb
    wph
    cW
    clvec
    wcel
    #
    @13
    lsatcmp.w
    cW
    lveclmod
    syl
    #
    vv
    cA
    cU
    @1
    @4
    cW
    clmod
    @5
    @4
    eqid
    #
    @1
    eqid
    #
    @5
    eqid
    #
    lsatcmp.a
    islsat
    syl
    mpbid
    wph
    @3
    @11
    vv
    @7
    wph
    @0
    @7
    wcel
    #
    cT
    @2
    wss
    #
    cT
    @2
    wceq
    #
    wb
    #
    @3
    @11
    wi
    @19
    @0
    @4
    wcel
    #
    @0
    @5
    wne
    #
    wa
    #
    wph
    @22
    @0
    @4
    @5
    eldifsn
    wph
    @25
    @22
    wph
    @25
    wa
    #
    @20
    @21
    @26
    @20
    @21
    @26
    @20
    wa
    #
    cT
    @6
    wne
    #
    @21
    wph
    @28
    @25
    @20
    wph
    cA
    cT
    cW
    @5
    @18
    lsatcmp.a
    @15
    lsatcmp.t
    lsatn0
    ad2antrr
    @27
    @21
    cT
    @6
    @27
    @21
    cT
    @6
    wceq
    #
    @27
    @14
    cT
    cW
    clss
    cfv
    #
    wcel
    #
    @23
    @20
    @21
    @29
    wo
    wph
    @14
    @25
    @20
    lsatcmp.w
    ad2antrr
    wph
    @31
    @25
    @20
    wph
    cA
    @30
    cT
    cW
    @30
    eqid
    #
    lsatcmp.a
    @15
    lsatcmp.t
    lsatlssel
    ad2antrr
    wph
    @23
    @24
    @20
    simplrl
    @26
    @20
    simpr
    @30
    cT
    @1
    @4
    cW
    @0
    @5
    @16
    @18
    @32
    @17
    lspsnat
    syl31anc
    ord
    necon1ad
    mpd
    ex
    cT
    @2
    eqimss
    impbid1
    ex
    syl5bi
    @3
    @11
    @22
    @3
    @9
    @20
    @10
    @21
    cU
    @2
    cT
    sseq2
    cU
    @2
    cT
    eqeq2
    bibi12d
    biimprcd
    syl6
    rexlimdv
    mpd
end
