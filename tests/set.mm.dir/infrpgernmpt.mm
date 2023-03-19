include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "nfv.mm"
include "eqid.mm"
include "rnmptssd.mm"
include "rnmptn0.mm"
include "wral.mm"
include "cr.mm"
include "wceq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "rnmptlb.mm"
include "infrpge.mm"
include "wcel.mm"
include "wa.mm"
include "simpll.mm"
include "simpr.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "ad2antlr.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfinf.mm"
include "nfov.mm"
include "nfbr.mm"
include "nfan.mm"
include "wi.mm"
include "id.mm"
include "eqcomd.mm"
include "adantl.mm"
include "simpl.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "a1d.mm"
include "reximdai.mm"
include "imp.mm"
include "syl21anc.mm"
include "rexlimdva2.mm"
include "mpd.mm"

theorem infrpgernmpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vz: setvar z
  assume infrpgernmpt.x: |- F/ x ph
  assume infrpgernmpt.a: |- ( ph -> A =/= (/) )
  assume infrpgernmpt.b: |- ( ( ph /\ x e. A ) -> B e. RR* )
  assume infrpgernmpt.y: |- ( ph -> E. y e. RR A. x e. A y <_ B )
  assume infrpgernmpt.c: |- ( ph -> C e. RR+ )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C x
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint A z
  disjoint w z
  disjoint x z
  disjoint B w
  disjoint B z
  disjoint C w
  disjoint ph w
  disjoint ph z
  assert |- ( ph -> E. x e. A B <_ ( inf ( ran ( x e. A |-> B ) , RR* , < ) +e C ) )

  proof
    wph
    vw
    cv
    #
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    cC
    cxad
    co
    #
    cle
    wbr
    #
    vw
    @2
    wrex
    cB
    @4
    cle
    wbr
    #
    vx
    cA
    wrex
    #
    wph
    vw
    vz
    vw
    @2
    cC
    wph
    vw
    nfv
    wph
    vx
    cA
    cB
    cxr
    @1
    infrpgernmpt.x
    @1
    eqid
    #
    infrpgernmpt.b
    rnmptssd
    wph
    vx
    cA
    cB
    @1
    cxr
    infrpgernmpt.x
    infrpgernmpt.b
    @8
    infrpgernmpt.a
    rnmptn0
    wph
    vx
    vw
    vz
    cA
    cB
    wph
    vy
    cv
    #
    cB
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vy
    cr
    wrex
    @0
    cB
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vw
    cr
    wrex
    infrpgernmpt.y
    @11
    @13
    vy
    vw
    cr
    @9
    @0
    wceq
    @10
    @12
    vx
    cA
    @9
    @0
    cB
    cle
    breq1
    ralbidv
    cbvrexv
    sylib
    rnmptlb
    infrpgernmpt.c
    infrpge
    wph
    @5
    @7
    vw
    @2
    wph
    @0
    @2
    wcel
    #
    wa
    #
    @5
    wa
    wph
    @5
    @0
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @7
    wph
    @14
    @5
    simpll
    @15
    @5
    simpr
    @14
    @17
    wph
    @5
    @14
    @17
    @0
    cvv
    wcel
    @14
    @17
    wb
    vw
    vex
    vx
    cA
    cB
    @0
    @1
    cvv
    @8
    elrnmpt
    ax-mp
    biimpi
    ad2antlr
    wph
    @5
    wa
    #
    @17
    @7
    @18
    @16
    @6
    vx
    cA
    wph
    @5
    vx
    infrpgernmpt.x
    vx
    @0
    @4
    cle
    vx
    @0
    nfcv
    vx
    cle
    nfcv
    vx
    @3
    cC
    cxad
    vx
    @2
    cxr
    clt
    vx
    @1
    vx
    cA
    cB
    nfmpt1
    nfrn
    vx
    cxr
    nfcv
    vx
    clt
    nfcv
    nfinf
    vx
    cxad
    nfcv
    vx
    cC
    nfcv
    nfov
    nfbr
    nfan
    @5
    vx
    cv
    cA
    wcel
    #
    @16
    @6
    wi
    #
    wi
    wph
    @5
    @20
    @19
    @5
    @16
    @6
    @5
    @16
    wa
    cB
    @0
    @4
    cle
    @16
    cB
    @0
    wceq
    @5
    @16
    @0
    cB
    @16
    id
    eqcomd
    adantl
    @5
    @16
    simpl
    eqbrtrd
    ex
    a1d
    adantl
    reximdai
    imp
    syl21anc
    rexlimdva2
    mpd
end
