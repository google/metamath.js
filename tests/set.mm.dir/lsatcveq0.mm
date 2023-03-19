include "wbr.mm"
include "csn.mm"
include "wceq.mm"
include "wpss.mm"
include "wa.mm"
include "clvec.mm"
include "wcel.mm"
include "adantr.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lsatlssel.mm"
include "simpr.mm"
include "lcvpss.mm"
include "ex.mm"
include "wi.mm"
include "lsatcv0.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "lsssn0.mm"
include "simp2.mm"
include "wss.mm"
include "lss0ss.mm"
include "syl2anc.mm"
include "simp3.mm"
include "lcvnbtwn3.mm"
include "3exp.mm"
include "mpd.mm"
include "syld.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem lsatcveq0
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cW: class W
  let c.0: class .0.
  assume lsatcveq0.o: |- .0. = ( 0g ` W )
  assume lsatcveq0.s: |- S = ( LSubSp ` W )
  assume lsatcveq0.a: |- A = ( LSAtoms ` W )
  assume lsatcveq0.c: |- C = ( <oL ` W )
  assume lsatcveq0.w: |- ( ph -> W e. LVec )
  assume lsatcveq0.u: |- ( ph -> U e. S )
  assume lsatcveq0.q: |- ( ph -> Q e. A )


  assert |- ( ph -> ( U C Q <-> U = { .0. } ) )

  proof
    wph
    cU
    cQ
    cC
    wbr
    #
    cU
    c.0
    csn
    #
    wceq
    #
    wph
    @0
    cU
    cQ
    wpss
    #
    @2
    wph
    @0
    @3
    wph
    @0
    wa
    cC
    cS
    cU
    cQ
    cW
    clvec
    lsatcveq0.s
    lsatcveq0.c
    wph
    cW
    clvec
    wcel
    #
    @0
    lsatcveq0.w
    adantr
    wph
    cU
    cS
    wcel
    #
    @0
    lsatcveq0.u
    adantr
    wph
    cQ
    cS
    wcel
    #
    @0
    wph
    cA
    cS
    cQ
    cW
    lsatcveq0.s
    lsatcveq0.a
    wph
    @4
    cW
    clmod
    wcel
    #
    lsatcveq0.w
    cW
    lveclmod
    syl
    #
    lsatcveq0.q
    lsatlssel
    #
    adantr
    wph
    @0
    simpr
    lcvpss
    ex
    wph
    @1
    cQ
    cC
    wbr
    #
    @3
    @2
    wi
    wph
    cA
    cC
    cQ
    cW
    c.0
    lsatcveq0.o
    lsatcveq0.a
    lsatcveq0.c
    lsatcveq0.w
    lsatcveq0.q
    lsatcv0
    #
    wph
    @10
    @3
    @2
    wph
    @10
    @3
    w3a
    cC
    @1
    cS
    cQ
    cU
    cW
    clvec
    lsatcveq0.s
    lsatcveq0.c
    wph
    @10
    @4
    @3
    lsatcveq0.w
    3ad2ant1
    wph
    @10
    @1
    cS
    wcel
    #
    @3
    wph
    @7
    @12
    @8
    cS
    cW
    c.0
    lsatcveq0.o
    lsatcveq0.s
    lsssn0
    syl
    3ad2ant1
    wph
    @10
    @6
    @3
    @9
    3ad2ant1
    wph
    @10
    @5
    @3
    lsatcveq0.u
    3ad2ant1
    wph
    @10
    @3
    simp2
    wph
    @10
    @1
    cU
    wss
    #
    @3
    wph
    @7
    @5
    @13
    @8
    lsatcveq0.u
    cS
    cW
    cU
    c.0
    lsatcveq0.o
    lsatcveq0.s
    lss0ss
    syl2anc
    3ad2ant1
    wph
    @10
    @3
    simp3
    lcvnbtwn3
    3exp
    mpd
    syld
    wph
    @0
    @2
    @10
    @11
    cU
    @1
    cQ
    cC
    breq1
    syl5ibrcom
    impbid
end
