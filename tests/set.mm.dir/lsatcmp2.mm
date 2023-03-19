include "wss.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "clvec.mm"
include "wcel.mm"
include "adantr.mm"
include "csn.mm"
include "wne.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lsatssn0.mm"
include "wi.mm"
include "ord.mm"
include "necon1ad.mm"
include "mpd.mm"
include "lsatcmp.mm"
include "mpbid.mm"
include "ex.mm"
include "eqimss.mm"
include "impbid1.mm"

theorem lsatcmp2
  let wph: wff ph
  let cA: class A
  let cT: class T
  let cU: class U
  let cW: class W
  let c.0: class .0.
  assume lsatcmp2.o: |- .0. = ( 0g ` W )
  assume lsatcmp2.a: |- A = ( LSAtoms ` W )
  assume lsatcmp2.w: |- ( ph -> W e. LVec )
  assume lsatcmp2.t: |- ( ph -> T e. A )
  assume lsatcmp2.u: |- ( ph -> ( U e. A \/ U = { .0. } ) )


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
    @0
    @1
    wph
    @0
    wa
    #
    @0
    @1
    wph
    @0
    simpr
    #
    @2
    cA
    cT
    cU
    cW
    lsatcmp2.a
    wph
    cW
    clvec
    wcel
    #
    @0
    lsatcmp2.w
    adantr
    wph
    cT
    cA
    wcel
    @0
    lsatcmp2.t
    adantr
    #
    @2
    cU
    c.0
    csn
    #
    wne
    #
    cU
    cA
    wcel
    #
    @2
    cA
    cT
    cU
    cW
    c.0
    lsatcmp2.o
    lsatcmp2.a
    wph
    cW
    clmod
    wcel
    #
    @0
    wph
    @4
    @9
    lsatcmp2.w
    cW
    lveclmod
    syl
    adantr
    @5
    @3
    lsatssn0
    wph
    @7
    @8
    wi
    @0
    wph
    @8
    cU
    @6
    wph
    @8
    cU
    @6
    wceq
    lsatcmp2.u
    ord
    necon1ad
    adantr
    mpd
    lsatcmp
    mpbid
    ex
    cT
    cU
    eqimss
    impbid1
end
