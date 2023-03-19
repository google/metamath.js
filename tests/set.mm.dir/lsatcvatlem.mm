include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wcel.mm"
include "clvec.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lssatomic.mm"
include "w3a.mm"
include "clcv.mm"
include "cfv.mm"
include "co.mm"
include "eqid.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "lsatlssel.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "wbr.mm"
include "wne.mm"
include "wn.mm"
include "wi.mm"
include "sseq1.mm"
include "biimpcd.mm"
include "necon3bd.mm"
include "3ad2ant3.mm"
include "mpd.mm"
include "lsatnem0.mm"
include "mpbid.mm"
include "lcvp.mm"
include "cabl.mm"
include "csubg.mm"
include "lmodabl.mm"
include "lsssssubg.mm"
include "sseldd.mm"
include "lsmcom.mm"
include "breqtrd.mm"
include "simp3.mm"
include "wpss.mm"
include "lsmub1.mm"
include "syl2anc.mm"
include "pssssd.mm"
include "sstrd.mm"
include "lsatexch1.mm"
include "wa.mm"
include "wb.mm"
include "lsmlub.mm"
include "mpbi2and.mm"
include "psssstrd.mm"
include "lcvnbtwn3.mm"
include "eqeltrd.mm"
include "rexlimdv3a.mm"

theorem lsatcvatlem
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  assume lsatcvat.o: |- .0. = ( 0g ` W )
  assume lsatcvat.s: |- S = ( LSubSp ` W )
  assume lsatcvat.p: |- .(+) = ( LSSum ` W )
  assume lsatcvat.a: |- A = ( LSAtoms ` W )
  assume lsatcvat.w: |- ( ph -> W e. LVec )
  assume lsatcvat.u: |- ( ph -> U e. S )
  assume lsatcvat.q: |- ( ph -> Q e. A )
  assume lsatcvat.r: |- ( ph -> R e. A )
  assume lsatcvat.n: |- ( ph -> U =/= { .0. } )
  assume lsatcvat.l: |- ( ph -> U C. ( Q .(+) R ) )
  assume lsatcvat.m: |- ( ph -> -. Q C_ U )


  assert |- ( ph -> U e. A )

  proof
    wph
    vx
    cv
    #
    cU
    wss
    #
    vx
    cA
    wrex
    cU
    cA
    wcel
    #
    wph
    cA
    cS
    cU
    cW
    c.0
    vx
    lsatcvat.s
    lsatcvat.o
    lsatcvat.a
    wph
    cW
    clvec
    wcel
    #
    cW
    clmod
    wcel
    #
    lsatcvat.w
    cW
    lveclmod
    syl
    #
    lsatcvat.u
    lsatcvat.n
    lssatomic
    wph
    @1
    @2
    vx
    cA
    wph
    @0
    cA
    wcel
    #
    @1
    w3a
    #
    cU
    @0
    cA
    @7
    cW
    clcv
    cfv
    #
    @0
    cS
    cQ
    @0
    c.po
    co
    #
    cU
    cW
    clvec
    lsatcvat.s
    @8
    eqid
    #
    wph
    @6
    @3
    @1
    lsatcvat.w
    3ad2ant1
    #
    @7
    cA
    cS
    @0
    cW
    lsatcvat.s
    lsatcvat.a
    wph
    @6
    @4
    @1
    @5
    3ad2ant1
    #
    wph
    @6
    @1
    simp2
    #
    lsatlssel
    #
    @7
    @4
    cQ
    cS
    wcel
    #
    @0
    cS
    wcel
    @9
    cS
    wcel
    @12
    wph
    @6
    @15
    @1
    wph
    cA
    cS
    cQ
    cW
    lsatcvat.s
    lsatcvat.a
    @5
    lsatcvat.q
    lsatlssel
    3ad2ant1
    #
    @14
    c.po
    cS
    cQ
    @0
    cW
    lsatcvat.s
    lsatcvat.p
    lsmcl
    syl3anc
    #
    wph
    @6
    cU
    cS
    wcel
    @1
    lsatcvat.u
    3ad2ant1
    @7
    @0
    @0
    cQ
    c.po
    co
    #
    @9
    @8
    @7
    @0
    cQ
    cin
    c.0
    csn
    wceq
    #
    @0
    @18
    @8
    wbr
    @7
    @0
    cQ
    wne
    #
    @19
    @7
    cQ
    cU
    wss
    #
    wn
    #
    @20
    wph
    @6
    @22
    @1
    lsatcvat.m
    3ad2ant1
    @1
    wph
    @22
    @20
    wi
    @6
    @1
    @21
    @0
    cQ
    @0
    cQ
    wceq
    @1
    @21
    @0
    cQ
    cU
    sseq1
    biimpcd
    necon3bd
    3ad2ant3
    mpd
    #
    @7
    cA
    @0
    cQ
    cW
    c.0
    lsatcvat.o
    lsatcvat.a
    @11
    @13
    wph
    @6
    cQ
    cA
    wcel
    @1
    lsatcvat.q
    3ad2ant1
    #
    lsatnem0
    mpbid
    @7
    cA
    @8
    c.po
    cQ
    cS
    @0
    cW
    c.0
    lsatcvat.s
    lsatcvat.p
    lsatcvat.o
    lsatcvat.a
    @10
    @11
    @14
    @24
    lcvp
    mpbid
    @7
    cW
    cabl
    wcel
    #
    @0
    cW
    csubg
    cfv
    #
    wcel
    #
    cQ
    @26
    wcel
    #
    @18
    @9
    wceq
    @7
    @4
    @25
    @12
    cW
    lmodabl
    syl
    @7
    cS
    @26
    @0
    @7
    @4
    cS
    @26
    wss
    @12
    cS
    cW
    lsatcvat.s
    lsssssubg
    syl
    #
    @14
    sseldd
    #
    @7
    cS
    @26
    cQ
    @29
    @16
    sseldd
    #
    c.po
    @0
    cQ
    cW
    lsatcvat.p
    lsmcom
    syl3anc
    breqtrd
    wph
    @6
    @1
    simp3
    #
    @7
    cU
    cQ
    cR
    c.po
    co
    #
    @9
    wph
    @6
    cU
    @33
    wpss
    @1
    lsatcvat.l
    3ad2ant1
    @7
    cQ
    @9
    wss
    #
    cR
    @9
    wss
    #
    @33
    @9
    wss
    #
    @7
    @28
    @27
    @34
    @31
    @30
    c.po
    cQ
    @0
    cW
    lsatcvat.p
    lsmub1
    syl2anc
    @7
    cA
    c.po
    @0
    cR
    cQ
    cW
    lsatcvat.p
    lsatcvat.a
    @11
    @13
    wph
    @6
    cR
    cA
    wcel
    @1
    lsatcvat.r
    3ad2ant1
    @24
    @7
    @0
    cU
    @33
    @32
    wph
    @6
    cU
    @33
    wss
    @1
    wph
    cU
    @33
    lsatcvat.l
    pssssd
    3ad2ant1
    sstrd
    @23
    lsatexch1
    @7
    @28
    cR
    @26
    wcel
    @9
    @26
    wcel
    @34
    @35
    wa
    @36
    wb
    @31
    @7
    cS
    @26
    cR
    @29
    wph
    @6
    cR
    cS
    wcel
    @1
    wph
    cA
    cS
    cR
    cW
    lsatcvat.s
    lsatcvat.a
    @5
    lsatcvat.r
    lsatlssel
    3ad2ant1
    sseldd
    @7
    cS
    @26
    @9
    @29
    @17
    sseldd
    c.po
    cQ
    cR
    @9
    cW
    lsatcvat.p
    lsmlub
    syl3anc
    mpbi2and
    psssstrd
    lcvnbtwn3
    @13
    eqeltrd
    rexlimdv3a
    mpd
end
