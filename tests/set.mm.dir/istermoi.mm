include "ctermo.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "weu.mm"
include "wral.mm"
include "crab.mm"
include "termoval.mm"
include "eleq2d.mm"
include "elrabi.mm"
include "syl6bi.mm"
include "imp.mm"
include "ccat.mm"
include "adantr.mm"
include "simpr.mm"
include "istermo.mm"
include "biimpd.mm"
include "impancom.mm"
include "jcai.mm"

theorem istermoi
  let wph: wff ph
  let cB: class B
  let cC: class C
  let vh: setvar h
  let cH: class H
  let cO: class O
  let vb: setvar b
  let va: setvar a
  assume isinitoi.b: |- B = ( Base ` C )
  assume isinitoi.h: |- H = ( Hom ` C )
  assume isinitoi.c: |- ( ph -> C e. Cat )

  disjoint B b
  disjoint C b
  disjoint C h
  disjoint b h
  disjoint O b
  disjoint O h
  disjoint B a
  disjoint a b
  disjoint C a
  disjoint a h
  disjoint O a
  assert |- ( ( ph /\ O e. ( TermO ` C ) ) -> ( O e. B /\ A. b e. B E! h h e. ( b H O ) ) )

  proof
    wph
    cO
    cC
    ctermo
    cfv
    #
    wcel
    #
    wa
    cO
    cB
    wcel
    #
    vh
    cv
    #
    vb
    cv
    #
    cO
    cH
    co
    wcel
    vh
    weu
    vb
    cB
    wral
    #
    wph
    @1
    @2
    wph
    @1
    cO
    @3
    @4
    va
    cv
    cH
    co
    wcel
    vh
    weu
    vb
    cB
    wral
    #
    va
    cB
    crab
    #
    wcel
    @2
    wph
    @0
    @7
    cO
    wph
    cB
    cC
    vh
    cH
    va
    vb
    isinitoi.c
    isinitoi.b
    isinitoi.h
    termoval
    eleq2d
    @6
    va
    cO
    cB
    elrabi
    syl6bi
    imp
    wph
    @2
    @1
    @5
    wph
    @2
    wa
    #
    @1
    @5
    @8
    cB
    cC
    vh
    cH
    cO
    vb
    isinitoi.b
    isinitoi.h
    wph
    cC
    ccat
    wcel
    @2
    isinitoi.c
    adantr
    wph
    @2
    simpr
    istermo
    biimpd
    impancom
    jcai
end
