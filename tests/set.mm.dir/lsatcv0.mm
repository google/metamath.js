include "csn.mm"
include "wbr.mm"
include "wpss.mm"
include "cv.mm"
include "wa.mm"
include "clss.mm"
include "cfv.mm"
include "wrex.mm"
include "wn.mm"
include "wss.mm"
include "wne.mm"
include "clmod.mm"
include "wcel.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "eqid.mm"
include "lsatlssel.mm"
include "lss0ss.mm"
include "syl2anc.mm"
include "lsatn0.mm"
include "necomd.mm"
include "df-pss.mm"
include "sylanbrc.mm"
include "clspn.mm"
include "wceq.mm"
include "cbs.mm"
include "cdif.mm"
include "wb.mm"
include "islsat.mm"
include "mpbid.mm"
include "wi.mm"
include "adantr.mm"
include "eldifi.mm"
include "adantl.mm"
include "eldifsni.mm"
include "lspsncv0.mm"
include "ex.mm"
include "psseq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "notbid.mm"
include "biimprcd.mm"
include "syl6.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "lsssn0.mm"
include "lcvbr.mm"
include "mpbir2and.mm"

theorem lsatcv0
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cQ: class Q
  let cW: class W
  let c.0: class .0.
  let vs: setvar s
  let vx: setvar x
  assume lsatcv0.o: |- .0. = ( 0g ` W )
  assume lsatcv0.a: |- A = ( LSAtoms ` W )
  assume lsatcv0.c: |- C = ( <oL ` W )
  assume lsatcv0.w: |- ( ph -> W e. LVec )
  assume lsatcv0.q: |- ( ph -> Q e. A )


  assert |- ( ph -> { .0. } C Q )

  proof
    wph
    c.0
    csn
    #
    cQ
    cC
    wbr
    @0
    cQ
    wpss
    #
    @0
    vs
    cv
    #
    wpss
    #
    @2
    cQ
    wpss
    #
    wa
    #
    vs
    cW
    clss
    cfv
    #
    wrex
    #
    wn
    #
    wph
    @0
    cQ
    wss
    #
    @0
    cQ
    wne
    @1
    wph
    cW
    clmod
    wcel
    #
    cQ
    @6
    wcel
    @9
    wph
    cW
    clvec
    wcel
    #
    @10
    lsatcv0.w
    cW
    lveclmod
    syl
    #
    wph
    cA
    @6
    cQ
    cW
    @6
    eqid
    #
    lsatcv0.a
    @12
    lsatcv0.q
    lsatlssel
    #
    @6
    cW
    cQ
    c.0
    lsatcv0.o
    @13
    lss0ss
    syl2anc
    wph
    cQ
    @0
    wph
    cA
    cQ
    cW
    c.0
    lsatcv0.o
    lsatcv0.a
    @12
    lsatcv0.q
    lsatn0
    necomd
    @0
    cQ
    df-pss
    sylanbrc
    wph
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
    @0
    cdif
    #
    wrex
    #
    @8
    wph
    cQ
    cA
    wcel
    #
    @21
    lsatcv0.q
    wph
    @10
    @22
    @21
    wb
    @12
    vx
    cA
    cQ
    @16
    @19
    cW
    clmod
    c.0
    @19
    eqid
    #
    @16
    eqid
    #
    lsatcv0.o
    lsatcv0.a
    islsat
    syl
    mpbid
    wph
    @18
    @8
    vx
    @20
    wph
    @15
    @20
    wcel
    #
    @3
    @2
    @17
    wpss
    #
    wa
    #
    vs
    @6
    wrex
    #
    wn
    #
    @18
    @8
    wi
    wph
    @25
    @29
    wph
    @25
    wa
    vs
    @6
    @16
    @19
    cW
    @15
    c.0
    @23
    lsatcv0.o
    @13
    @24
    wph
    @11
    @25
    lsatcv0.w
    adantr
    @25
    @15
    @19
    wcel
    wph
    @15
    @19
    @0
    eldifi
    adantl
    @25
    @15
    c.0
    wne
    wph
    @15
    @19
    c.0
    eldifsni
    adantl
    lspsncv0
    ex
    @18
    @8
    @29
    @18
    @7
    @28
    @18
    @5
    @27
    vs
    @6
    @18
    @4
    @26
    @3
    cQ
    @17
    @2
    psseq2
    anbi2d
    rexbidv
    notbid
    biimprcd
    syl6
    rexlimdv
    mpd
    wph
    cC
    @6
    @0
    cQ
    cW
    clvec
    vs
    @13
    lsatcv0.c
    lsatcv0.w
    wph
    @10
    @0
    @6
    wcel
    @12
    @6
    cW
    c.0
    lsatcv0.o
    @13
    lsssn0
    syl
    @14
    lcvbr
    mpbir2and
end
