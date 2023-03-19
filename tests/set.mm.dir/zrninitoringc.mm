include "cinito.mm"
include "cfv.mm"
include "wnel.mm"
include "cv.mm"
include "chom.mm"
include "co.mm"
include "wcel.mm"
include "weu.mm"
include "cbs.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "cnzr.mm"
include "wa.mm"
include "wex.mm"
include "wal.mm"
include "c0.mm"
include "wceq.mm"
include "crh.mm"
include "eqid.mm"
include "ad2antrr.mm"
include "crg.mm"
include "cin.mm"
include "eldifad.mm"
include "elind.mm"
include "ringcbas.mm"
include "eleqtrrd.mm"
include "simplr.mm"
include "ringchom.mm"
include "cdif.mm"
include "adantr.mm"
include "nrhmzr.mm"
include "sylan.mm"
include "eqtrd.mm"
include "eq0.mm"
include "sylib.mm"
include "alnex.mm"
include "euex.mm"
include "nsyl.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "rexnal.mm"
include "df-nel.mm"
include "ccat.mm"
include "ringccat.mm"
include "syl.mm"
include "isinito.mm"
include "notbid.mm"
include "syl5bb.mm"
include "mpbird.mm"

theorem zrninitoringc
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cV: class V
  let cZ: class Z
  let vr: setvar r
  let va: setvar a
  let vh: setvar h
  let vx: setvar x
  let vk: setvar k
  assume zrtermoringc.u: |- ( ph -> U e. V )
  assume zrtermoringc.c: |- C = ( RingCat ` U )
  assume zrtermoringc.z: |- ( ph -> Z e. ( Ring \ NzRing ) )
  assume zrtermoringc.e: |- ( ph -> Z e. U )
  assume zrninitoringc.e: |- ( ph -> E. r e. ( Base ` C ) r e. NzRing )

  disjoint C r
  disjoint Z r
  disjoint ph r
  disjoint C a
  disjoint C h
  disjoint C x
  disjoint a h
  disjoint a r
  disjoint a x
  disjoint h r
  disjoint h x
  disjoint r x
  disjoint Z a
  disjoint Z h
  disjoint Z x
  disjoint a ph
  disjoint h ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> Z e/ ( InitO ` C ) )

  proof
    wph
    cZ
    cC
    cinito
    cfv
    #
    wnel
    #
    vh
    cv
    cZ
    vr
    cv
    #
    cC
    chom
    cfv
    #
    co
    #
    wcel
    #
    vh
    weu
    #
    vr
    cC
    cbs
    cfv
    #
    wral
    #
    wn
    #
    wph
    @6
    wn
    #
    vr
    @7
    wrex
    #
    @9
    wph
    @2
    cnzr
    wcel
    #
    vr
    @7
    wrex
    @11
    zrninitoringc.e
    wph
    @12
    @10
    vr
    @7
    wph
    @2
    @7
    wcel
    #
    wa
    #
    @12
    @10
    @14
    @12
    wa
    #
    @5
    vh
    wex
    #
    @6
    @15
    @5
    wn
    vh
    wal
    #
    @16
    wn
    @15
    @4
    c0
    wceq
    @17
    @15
    @4
    cZ
    @2
    crh
    co
    #
    c0
    @15
    @7
    cC
    cU
    @3
    cV
    cZ
    @2
    zrtermoringc.c
    @7
    eqid
    #
    wph
    cU
    cV
    wcel
    #
    @13
    @12
    zrtermoringc.u
    ad2antrr
    @3
    eqid
    #
    wph
    cZ
    @7
    wcel
    @13
    @12
    wph
    cZ
    cU
    crg
    cin
    @7
    wph
    cU
    crg
    cZ
    zrtermoringc.e
    wph
    cZ
    crg
    cnzr
    zrtermoringc.z
    eldifad
    elind
    wph
    @7
    cC
    cU
    cV
    zrtermoringc.c
    @19
    zrtermoringc.u
    ringcbas
    eleqtrrd
    #
    ad2antrr
    wph
    @13
    @12
    simplr
    ringchom
    @14
    cZ
    crg
    cnzr
    cdif
    wcel
    #
    @12
    @18
    c0
    wceq
    wph
    @23
    @13
    zrtermoringc.z
    adantr
    @2
    cZ
    nrhmzr
    sylan
    eqtrd
    vh
    @4
    eq0
    sylib
    @5
    vh
    alnex
    sylib
    @5
    vh
    euex
    nsyl
    ex
    reximdva
    mpd
    @6
    vr
    @7
    rexnal
    sylib
    @1
    cZ
    @0
    wcel
    #
    wn
    wph
    @9
    cZ
    @0
    df-nel
    wph
    @24
    @8
    wph
    @7
    cC
    vh
    @3
    cZ
    vr
    @19
    @21
    wph
    @20
    cC
    ccat
    wcel
    zrtermoringc.u
    cC
    cU
    cV
    zrtermoringc.c
    ringccat
    syl
    @22
    isinito
    notbid
    syl5bb
    mpbird
end
