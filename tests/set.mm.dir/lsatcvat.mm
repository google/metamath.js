include "wss.mm"
include "wn.mm"
include "wcel.mm"
include "wa.mm"
include "clvec.mm"
include "adantr.mm"
include "csn.mm"
include "wne.mm"
include "co.mm"
include "wpss.mm"
include "simpr.mm"
include "lsatcvatlem.mm"
include "cabl.mm"
include "csubg.mm"
include "cfv.mm"
include "wceq.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lmodabl.mm"
include "lsssssubg.mm"
include "lsatlssel.mm"
include "sseldd.mm"
include "lsmcom.mm"
include "syl3anc.mm"
include "psseq2d.mm"
include "mpbid.mm"
include "wo.mm"
include "wb.mm"
include "lsmlub.mm"
include "ssnpss.mm"
include "syl6bi.mm"
include "con2d.mm"
include "ianor.mm"
include "syl6ib.mm"
include "mpd.mm"
include "mpjaodan.mm"

theorem lsatcvat
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cW: class W
  let c.0: class .0.
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


  assert |- ( ph -> U e. A )

  proof
    wph
    cQ
    cU
    wss
    #
    wn
    #
    cU
    cA
    wcel
    cR
    cU
    wss
    #
    wn
    #
    wph
    @1
    wa
    cA
    c.po
    cQ
    cR
    cS
    cU
    cW
    c.0
    lsatcvat.o
    lsatcvat.s
    lsatcvat.p
    lsatcvat.a
    wph
    cW
    clvec
    wcel
    #
    @1
    lsatcvat.w
    adantr
    wph
    cU
    cS
    wcel
    #
    @1
    lsatcvat.u
    adantr
    wph
    cQ
    cA
    wcel
    #
    @1
    lsatcvat.q
    adantr
    wph
    cR
    cA
    wcel
    #
    @1
    lsatcvat.r
    adantr
    wph
    cU
    c.0
    csn
    wne
    #
    @1
    lsatcvat.n
    adantr
    wph
    cU
    cQ
    cR
    c.po
    co
    #
    wpss
    #
    @1
    lsatcvat.l
    adantr
    wph
    @1
    simpr
    lsatcvatlem
    wph
    @3
    wa
    cA
    c.po
    cR
    cQ
    cS
    cU
    cW
    c.0
    lsatcvat.o
    lsatcvat.s
    lsatcvat.p
    lsatcvat.a
    wph
    @4
    @3
    lsatcvat.w
    adantr
    wph
    @5
    @3
    lsatcvat.u
    adantr
    wph
    @7
    @3
    lsatcvat.r
    adantr
    wph
    @6
    @3
    lsatcvat.q
    adantr
    wph
    @8
    @3
    lsatcvat.n
    adantr
    wph
    cU
    cR
    cQ
    c.po
    co
    #
    wpss
    #
    @3
    wph
    @10
    @12
    lsatcvat.l
    wph
    @9
    @11
    cU
    wph
    cW
    cabl
    wcel
    #
    cQ
    cW
    csubg
    cfv
    #
    wcel
    #
    cR
    @14
    wcel
    #
    @9
    @11
    wceq
    wph
    cW
    clmod
    wcel
    #
    @13
    wph
    @4
    @17
    lsatcvat.w
    cW
    lveclmod
    syl
    #
    cW
    lmodabl
    syl
    wph
    cS
    @14
    cQ
    wph
    @17
    cS
    @14
    wss
    @18
    cS
    cW
    lsatcvat.s
    lsssssubg
    syl
    #
    wph
    cA
    cS
    cQ
    cW
    lsatcvat.s
    lsatcvat.a
    @18
    lsatcvat.q
    lsatlssel
    sseldd
    #
    wph
    cS
    @14
    cR
    @19
    wph
    cA
    cS
    cR
    cW
    lsatcvat.s
    lsatcvat.a
    @18
    lsatcvat.r
    lsatlssel
    sseldd
    #
    c.po
    cQ
    cR
    cW
    lsatcvat.p
    lsmcom
    syl3anc
    psseq2d
    mpbid
    adantr
    wph
    @3
    simpr
    lsatcvatlem
    wph
    @10
    @1
    @3
    wo
    #
    lsatcvat.l
    wph
    @10
    @0
    @2
    wa
    #
    wn
    @22
    wph
    @23
    @10
    wph
    @23
    @9
    cU
    wss
    #
    @10
    wn
    wph
    @15
    @16
    cU
    @14
    wcel
    @23
    @24
    wb
    @20
    @21
    wph
    cS
    @14
    cU
    @19
    lsatcvat.u
    sseldd
    c.po
    cQ
    cR
    cU
    cW
    lsatcvat.p
    lsmlub
    syl3anc
    @9
    cU
    ssnpss
    syl6bi
    con2d
    @0
    @2
    ianor
    syl6ib
    mpd
    mpjaodan
end
