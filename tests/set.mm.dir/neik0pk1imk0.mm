include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "pwidg.mm"
include "syl.mm"
include "wceq.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "ralimdv.mm"
include "mpd.mm"
include "r19.23v.mm"
include "biimpi.mm"
include "a1i.mm"
include "c0.mm"
include "wne.mm"
include "wex.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "elpwid.mm"
include "sseld.mm"
include "ancrd.mm"
include "eximdv.mm"
include "n0.mm"
include "df-rex.mm"
include "3imtr4g.mm"
include "imp.mm"
include "wal.mm"
include "elpwi.mm"
include "syl6.mm"
include "alrimiv.mm"
include "alral.mm"
include "adantr.mm"
include "r19.29imd.mm"
include "ex.mm"
include "ralimdva.mm"
include "ralim.mm"
include "sylc.mm"

theorem neik0pk1imk0
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cB: class B
  let cN: class N
  let cV: class V
  let vs: setvar s
  assume neik0pk1imk0.bex: |- ( ph -> B e. V )
  assume neik0pk1imk0.n: |- ( ph -> N e. ( ~P ~P B ^m B ) )
  assume neik0pk1imk0.k0p: |- ( ph -> A. x e. B ( N ` x ) =/= (/) )
  assume neik0pk1imk0.k1: |- ( ph -> A. x e. B A. s e. ~P B A. t e. ~P B ( ( s e. ( N ` x ) /\ s C_ t ) -> t e. ( N ` x ) ) )

  disjoint B s
  disjoint B t
  disjoint s t
  disjoint N s
  disjoint N t
  disjoint ph s
  disjoint ph x
  disjoint s x
  disjoint t x
  assert |- ( ph -> A. x e. B B e. ( N ` x ) )

  proof
    wph
    vs
    cv
    #
    vx
    cv
    #
    cN
    cfv
    #
    wcel
    #
    @0
    cB
    wss
    #
    wa
    #
    vs
    cB
    cpw
    #
    wrex
    #
    cB
    @2
    wcel
    #
    wi
    #
    vx
    cB
    wral
    #
    @7
    vx
    cB
    wral
    #
    @8
    vx
    cB
    wral
    wph
    @5
    @8
    wi
    #
    vs
    @6
    wral
    #
    vx
    cB
    wral
    #
    @10
    wph
    @3
    @0
    vt
    cv
    #
    wss
    #
    wa
    #
    @15
    @2
    wcel
    #
    wi
    #
    vt
    @6
    wral
    #
    vs
    @6
    wral
    #
    vx
    cB
    wral
    @14
    neik0pk1imk0.k1
    wph
    @21
    @13
    vx
    cB
    wph
    @20
    @12
    vs
    @6
    wph
    cB
    @6
    wcel
    #
    @20
    @12
    wi
    wph
    cB
    cV
    wcel
    @22
    neik0pk1imk0.bex
    cB
    cV
    pwidg
    syl
    @19
    @12
    vt
    cB
    @6
    @15
    cB
    wceq
    #
    @17
    @5
    @18
    @8
    @23
    @16
    @4
    @3
    @15
    cB
    @0
    sseq2
    anbi2d
    @15
    cB
    @2
    eleq1
    imbi12d
    rspcv
    syl
    ralimdv
    ralimdv
    mpd
    wph
    @13
    @9
    vx
    cB
    @13
    @9
    wi
    wph
    @13
    @9
    @5
    @8
    vs
    @6
    r19.23v
    biimpi
    a1i
    ralimdv
    mpd
    wph
    @2
    c0
    wne
    #
    vx
    cB
    wral
    @11
    neik0pk1imk0.k0p
    wph
    @24
    @7
    vx
    cB
    wph
    @1
    cB
    wcel
    wa
    #
    @24
    @7
    @25
    @24
    wa
    @3
    @4
    vs
    @6
    @25
    @24
    @3
    vs
    @6
    wrex
    #
    @25
    @3
    vs
    wex
    @0
    @6
    wcel
    #
    @3
    wa
    #
    vs
    wex
    @24
    @26
    @25
    @3
    @28
    vs
    @25
    @3
    @27
    @25
    @2
    @6
    @0
    @25
    @2
    @6
    wph
    cB
    @6
    cpw
    #
    @1
    cN
    wph
    cN
    @29
    cB
    cmap
    co
    wcel
    cB
    @29
    cN
    wf
    neik0pk1imk0.n
    cN
    @29
    cB
    elmapi
    syl
    ffvelrnda
    elpwid
    sseld
    #
    ancrd
    eximdv
    vs
    @2
    n0
    @3
    vs
    @6
    df-rex
    3imtr4g
    imp
    @25
    @3
    @4
    wi
    #
    vs
    @6
    wral
    #
    @24
    @25
    @31
    vs
    wal
    @32
    @25
    @31
    vs
    @25
    @3
    @27
    @4
    @30
    @0
    cB
    elpwi
    syl6
    alrimiv
    @31
    vs
    @6
    alral
    syl
    adantr
    r19.29imd
    ex
    ralimdva
    mpd
    @7
    @8
    vx
    cB
    ralim
    sylc
end
