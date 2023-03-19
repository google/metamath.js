include "cmpt.mm"
include "cdm.mm"
include "cr.mm"
include "wss.mm"
include "co1.mm"
include "wcel.mm"
include "clo1.mm"
include "wi.mm"
include "o1dm.mm"
include "a1i.mm"
include "lo1dm.mm"
include "wb.mm"
include "wral.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "syl.mm"
include "sseq1d.mm"
include "cneg.mm"
include "wa.mm"
include "simpr.mm"
include "cv.mm"
include "renegcld.mm"
include "adantlr.mm"
include "adantr.mm"
include "cle.mm"
include "wbr.mm"
include "lenegd.mm"
include "mpbid.mm"
include "ad2ant2r.mm"
include "ello1d.mm"
include "o1lo1.mm"
include "rbaibd.mm"
include "syldan.mm"
include "ex.mm"
include "sylbid.mm"
include "pm5.21ndd.mm"

theorem o1lo12
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cM: class M
  let vc: setvar c
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  assume o1lo1.1: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume o1lo12.2: |- ( ph -> M e. RR )
  assume o1lo12.3: |- ( ( ph /\ x e. A ) -> M <_ B )

  disjoint A x
  disjoint M x
  disjoint ph x
  disjoint c m
  disjoint c n
  disjoint c p
  disjoint c x
  disjoint A c
  disjoint m n
  disjoint m p
  disjoint m x
  disjoint A m
  disjoint n p
  disjoint n x
  disjoint A n
  disjoint p x
  disjoint A p
  disjoint B c
  disjoint B m
  disjoint B n
  disjoint B p
  disjoint c ph
  disjoint m ph
  disjoint n ph
  disjoint p ph
  assert |- ( ph -> ( ( x e. A |-> B ) e. O(1) <-> ( x e. A |-> B ) e. <_O(1) ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    cdm
    #
    cr
    wss
    #
    @0
    co1
    wcel
    #
    @0
    clo1
    wcel
    #
    @3
    @2
    wi
    wph
    @0
    o1dm
    a1i
    @4
    @2
    wi
    wph
    @0
    lo1dm
    a1i
    wph
    @2
    cA
    cr
    wss
    #
    @3
    @4
    wb
    #
    wph
    @1
    cA
    cr
    wph
    cB
    cr
    wcel
    #
    vx
    cA
    wral
    @1
    cA
    wceq
    wph
    @7
    vx
    cA
    o1lo1.1
    ralrimiva
    vx
    cA
    cB
    cr
    dmmptg
    syl
    sseq1d
    wph
    @5
    @6
    wph
    @5
    vx
    cA
    cB
    cneg
    #
    cmpt
    clo1
    wcel
    #
    @6
    wph
    @5
    wa
    #
    vx
    cA
    @8
    cM
    cM
    cneg
    #
    wph
    @5
    simpr
    wph
    vx
    cv
    #
    cA
    wcel
    #
    @8
    cr
    wcel
    @5
    wph
    @13
    wa
    #
    cB
    o1lo1.1
    renegcld
    adantlr
    wph
    cM
    cr
    wcel
    #
    @5
    o1lo12.2
    adantr
    #
    @10
    cM
    @16
    renegcld
    wph
    @13
    @8
    @11
    cle
    wbr
    #
    @5
    cM
    @12
    cle
    wbr
    @14
    cM
    cB
    cle
    wbr
    @17
    o1lo12.3
    @14
    cM
    cB
    wph
    @15
    @13
    o1lo12.2
    adantr
    o1lo1.1
    lenegd
    mpbid
    ad2ant2r
    ello1d
    wph
    @3
    @4
    @9
    wph
    vx
    cA
    cB
    o1lo1.1
    o1lo1
    rbaibd
    syldan
    ex
    sylbid
    pm5.21ndd
end
