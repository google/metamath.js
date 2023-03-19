include "wss.mm"
include "wn.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "c0g.mm"
include "cdif.mm"
include "wrex.mm"
include "wcel.mm"
include "clvec.mm"
include "wb.mm"
include "eqid.mm"
include "islsat.mm"
include "syl.mm"
include "mpbid.mm"
include "adantr.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "eldifi.mm"
include "3ad2ant2.mm"
include "simp1r.mm"
include "simp3.mm"
include "sseq1d.mm"
include "mtbid.mm"
include "lsmcv2.mm"
include "oveq2d.mm"
include "breqtrrd.mm"
include "rexlimdv3a.mm"
include "mpd.mm"
include "wpss.mm"
include "clmod.mm"
include "lveclmod.mm"
include "lsatlssel.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "simpr.mm"
include "lcvpss.mm"
include "csubg.mm"
include "lsssssubg.mm"
include "sseldd.mm"
include "lssnle.mm"
include "mpbird.mm"
include "impbida.mm"

theorem lcv1
  let wph: wff ph
  let cA: class A
  let cC: class C
  let c.po: class .(+)
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cW: class W
  let vx: setvar x
  assume lcv1.s: |- S = ( LSubSp ` W )
  assume lcv1.p: |- .(+) = ( LSSum ` W )
  assume lcv1.a: |- A = ( LSAtoms ` W )
  assume lcv1.c: |- C = ( <oL ` W )
  assume lcv1.w: |- ( ph -> W e. LVec )
  assume lcv1.u: |- ( ph -> U e. S )
  assume lcv1.q: |- ( ph -> Q e. A )


  assert |- ( ph -> ( -. Q C_ U <-> U C ( U .(+) Q ) ) )

  proof
    wph
    cQ
    cU
    wss
    #
    wn
    #
    cU
    cU
    cQ
    c.po
    co
    #
    cC
    wbr
    #
    wph
    @1
    wa
    #
    cQ
    vx
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
    vx
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
    @3
    wph
    @13
    @1
    wph
    cQ
    cA
    wcel
    #
    @13
    lcv1.q
    wph
    cW
    clvec
    wcel
    #
    @14
    @13
    wb
    lcv1.w
    vx
    cA
    cQ
    @6
    @9
    cW
    clvec
    @10
    @9
    eqid
    #
    @6
    eqid
    #
    @10
    eqid
    lcv1.a
    islsat
    syl
    mpbid
    adantr
    @4
    @8
    @3
    vx
    @12
    @4
    @5
    @12
    wcel
    #
    @8
    w3a
    #
    cU
    cU
    @7
    c.po
    co
    @2
    cC
    @19
    cC
    c.po
    cS
    cU
    @6
    @9
    cW
    @5
    @16
    lcv1.s
    @17
    lcv1.p
    lcv1.c
    @4
    @18
    @15
    @8
    wph
    @15
    @1
    lcv1.w
    adantr
    3ad2ant1
    @4
    @18
    cU
    cS
    wcel
    #
    @8
    wph
    @20
    @1
    lcv1.u
    adantr
    3ad2ant1
    @18
    @4
    @5
    @9
    wcel
    @8
    @5
    @9
    @11
    eldifi
    3ad2ant2
    @19
    @0
    @7
    cU
    wss
    wph
    @1
    @18
    @8
    simp1r
    @19
    cQ
    @7
    cU
    @4
    @18
    @8
    simp3
    #
    sseq1d
    mtbid
    lsmcv2
    @19
    cQ
    @7
    cU
    c.po
    @21
    oveq2d
    breqtrrd
    rexlimdv3a
    mpd
    wph
    @3
    wa
    #
    @1
    cU
    @2
    wpss
    #
    @22
    cC
    cS
    cU
    @2
    cW
    clvec
    lcv1.s
    lcv1.c
    wph
    @15
    @3
    lcv1.w
    adantr
    wph
    @20
    @3
    lcv1.u
    adantr
    wph
    @2
    cS
    wcel
    #
    @3
    wph
    cW
    clmod
    wcel
    #
    @20
    cQ
    cS
    wcel
    @24
    wph
    @15
    @25
    lcv1.w
    cW
    lveclmod
    syl
    #
    lcv1.u
    wph
    cA
    cS
    cQ
    cW
    lcv1.s
    lcv1.a
    @26
    lcv1.q
    lsatlssel
    #
    c.po
    cS
    cU
    cQ
    cW
    lcv1.s
    lcv1.p
    lsmcl
    syl3anc
    adantr
    wph
    @3
    simpr
    lcvpss
    wph
    @1
    @23
    wb
    @3
    wph
    c.po
    cU
    cQ
    cW
    lcv1.p
    wph
    cS
    cW
    csubg
    cfv
    #
    cU
    wph
    @25
    cS
    @28
    wss
    @26
    cS
    cW
    lcv1.s
    lsssssubg
    syl
    #
    lcv1.u
    sseldd
    wph
    cS
    @28
    cQ
    @29
    @27
    sseldd
    lssnle
    adantr
    mpbird
    impbida
end
