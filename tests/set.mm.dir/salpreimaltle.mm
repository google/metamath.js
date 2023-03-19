include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "clt.mm"
include "ciin.mm"
include "preimaleiinlt.mm"
include "com.mm"
include "cdom.mm"
include "nnct.mm"
include "a1i.mm"
include "c0.mm"
include "wne.mm"
include "nnn0.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "simpl.mm"
include "nnrecre.mm"
include "adantl.mm"
include "readdcld.mm"
include "sylan.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfim.mm"
include "ovex.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "breq2.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtoclf.mm"
include "syl2anc.mm"
include "saliincl.mm"
include "eqeltrd.mm"

theorem salpreimaltle
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let va: setvar a
  let vn: setvar n
  let vk: setvar k
  assume salpreimaltle.x: |- F/ x ph
  assume salpreimaltle.a: |- F/ a ph
  assume salpreimaltle.s: |- ( ph -> S e. SAlg )
  assume salpreimaltle.b: |- ( ( ph /\ x e. A ) -> B e. RR* )
  assume salpreimaltle.p: |- ( ( ph /\ a e. RR ) -> { x e. A | B < a } e. S )
  assume salpreimaltle.c: |- ( ph -> C e. RR )

  disjoint A a
  disjoint B a
  disjoint C a
  disjoint C x
  disjoint a x
  disjoint S a
  disjoint A n
  disjoint a n
  disjoint B n
  disjoint C n
  disjoint n x
  disjoint S n
  disjoint n ph
  disjoint k x
  assert |- ( ph -> { x e. A | B <_ C } e. S )

  proof
    wph
    cB
    cC
    cle
    wbr
    vx
    cA
    crab
    vn
    cn
    cB
    cC
    c1
    vn
    cv
    #
    cdiv
    co
    #
    caddc
    co
    #
    clt
    wbr
    #
    vx
    cA
    crab
    #
    ciin
    cS
    wph
    vx
    cA
    cB
    cC
    vn
    salpreimaltle.x
    salpreimaltle.b
    salpreimaltle.c
    preimaleiinlt
    wph
    cS
    vn
    @4
    cn
    salpreimaltle.s
    cn
    com
    cdom
    wbr
    wph
    nnct
    a1i
    cn
    c0
    wne
    wph
    nnn0
    a1i
    wph
    @0
    cn
    wcel
    #
    wa
    wph
    @2
    cr
    wcel
    #
    @4
    cS
    wcel
    #
    wph
    @5
    simpl
    wph
    cC
    cr
    wcel
    #
    @5
    @6
    salpreimaltle.c
    @8
    @5
    wa
    cC
    @1
    @8
    @5
    simpl
    @5
    @1
    cr
    wcel
    @8
    @0
    nnrecre
    adantl
    readdcld
    sylan
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    #
    cB
    @9
    clt
    wbr
    #
    vx
    cA
    crab
    #
    cS
    wcel
    #
    wi
    wph
    @6
    wa
    #
    @7
    wi
    va
    @2
    @15
    @7
    va
    wph
    @6
    va
    salpreimaltle.a
    @6
    va
    nfv
    nfan
    @7
    va
    nfv
    nfim
    cC
    @1
    caddc
    ovex
    @9
    @2
    wceq
    #
    @11
    @15
    @14
    @7
    @16
    @10
    @6
    wph
    @9
    @2
    cr
    eleq1
    anbi2d
    @16
    @13
    @4
    cS
    @16
    @12
    @3
    vx
    cA
    @9
    @2
    cB
    clt
    breq2
    rabbidv
    eleq1d
    imbi12d
    salpreimaltle.p
    vtoclf
    syl2anc
    saliincl
    eqeltrd
end
