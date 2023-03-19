include "cmpt.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "wcel.mm"
include "wb.mm"
include "eqid.mm"
include "rnmptssd.mm"
include "rnmptn0.mm"
include "rnmptbdd.mm"
include "suprleub.mm"
include "syl31anc.mm"
include "wa.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfv.mm"
include "nfral.mm"
include "nfan.mm"
include "simpr.mm"
include "elrnmpt1.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "simplr.mm"
include "breq1.mm"
include "rspcva.mm"
include "ex.mm"
include "ralrimi.mm"
include "wi.mm"
include "wceq.mm"
include "cvv.mm"
include "vex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "adantl.mm"
include "nfra1.mm"
include "rspa.mm"
include "biimprcd.mm"
include "syl.mm"
include "rexlimd.mm"
include "adantr.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "a1i.mm"
include "impbid.mm"
include "bitrd.mm"

theorem suprleubrnmpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vz: setvar z
  assume suprleubrnmpt.x: |- F/ x ph
  assume suprleubrnmpt.a: |- ( ph -> A =/= (/) )
  assume suprleubrnmpt.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume suprleubrnmpt.e: |- ( ph -> E. y e. RR A. x e. A B <_ y )
  assume suprleubrnmpt.c: |- ( ph -> C e. RR )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C x
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint A z
  disjoint x z
  disjoint B w
  disjoint B z
  disjoint C z
  assert |- ( ph -> ( sup ( ran ( x e. A |-> B ) , RR , < ) <_ C <-> A. x e. A B <_ C ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    cC
    cle
    wbr
    #
    vz
    cv
    #
    cC
    cle
    wbr
    #
    vz
    @1
    wral
    #
    cB
    cC
    cle
    wbr
    #
    vx
    cA
    wral
    #
    wph
    @1
    cr
    wss
    @1
    c0
    wne
    vw
    cv
    vy
    cv
    cle
    wbr
    vw
    @1
    wral
    vy
    cr
    wrex
    cC
    cr
    wcel
    @2
    @5
    wb
    wph
    vx
    cA
    cB
    cr
    @0
    suprleubrnmpt.x
    @0
    eqid
    #
    suprleubrnmpt.b
    rnmptssd
    wph
    vx
    cA
    cB
    @0
    cr
    suprleubrnmpt.x
    suprleubrnmpt.b
    @8
    suprleubrnmpt.a
    rnmptn0
    wph
    vx
    vy
    vw
    cA
    cB
    suprleubrnmpt.x
    suprleubrnmpt.e
    rnmptbdd
    suprleubrnmpt.c
    vy
    vw
    vz
    @1
    cC
    suprleub
    syl31anc
    wph
    @5
    @7
    wph
    @5
    @7
    wph
    @5
    wa
    #
    @6
    vx
    cA
    wph
    @5
    vx
    suprleubrnmpt.x
    @4
    vx
    vz
    @1
    vx
    @0
    vx
    cA
    cB
    nfmpt1
    nfrn
    @4
    vx
    nfv
    #
    nfral
    nfan
    @9
    vx
    cv
    cA
    wcel
    #
    @6
    @9
    @11
    wa
    cB
    @1
    wcel
    #
    @5
    @6
    wph
    @11
    @12
    @5
    wph
    @11
    wa
    @11
    cB
    cr
    wcel
    @12
    wph
    @11
    simpr
    suprleubrnmpt.b
    vx
    cA
    cB
    @0
    cr
    @8
    elrnmpt1
    syl2anc
    adantlr
    wph
    @5
    @11
    simplr
    @4
    @6
    vz
    cB
    @1
    @3
    cB
    cC
    cle
    breq1
    #
    rspcva
    syl2anc
    ex
    ralrimi
    ex
    @7
    @5
    wi
    wph
    @7
    @4
    vz
    @1
    @7
    @3
    @1
    wcel
    #
    wa
    @3
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @4
    @14
    @16
    @7
    @14
    @16
    @3
    cvv
    wcel
    @14
    @16
    wb
    vz
    vex
    vx
    cA
    cB
    @3
    @0
    cvv
    @8
    elrnmpt
    ax-mp
    biimpi
    adantl
    @7
    @16
    @4
    wi
    @14
    @7
    @15
    @4
    vx
    cA
    @6
    vx
    cA
    nfra1
    @10
    @7
    @11
    @15
    @4
    wi
    #
    @7
    @11
    wa
    @6
    @17
    @6
    vx
    cA
    rspa
    @15
    @4
    @6
    @13
    biimprcd
    syl
    ex
    rexlimd
    adantr
    mpd
    ralrimiva
    a1i
    impbid
    bitrd
end
