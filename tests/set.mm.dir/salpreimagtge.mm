include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "clt.mm"
include "ciin.mm"
include "preimageiingt.mm"
include "com.mm"
include "cdom.mm"
include "nnct.mm"
include "a1i.mm"
include "c0.mm"
include "wne.mm"
include "nnn0.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "adantr.mm"
include "nnrecre.mm"
include "adantl.mm"
include "resubcld.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfim.mm"
include "ovex.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "breq1.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtoclf.mm"
include "syldan.mm"
include "saliincl.mm"
include "eqeltrd.mm"

theorem salpreimagtge
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let va: setvar a
  let vn: setvar n
  let vk: setvar k
  assume salpreimagtge.x: |- F/ x ph
  assume salpreimagtge.a: |- F/ a ph
  assume salpreimagtge.s: |- ( ph -> S e. SAlg )
  assume salpreimagtge.b: |- ( ( ph /\ x e. A ) -> B e. RR* )
  assume salpreimagtge.p: |- ( ( ph /\ a e. RR ) -> { x e. A | a < B } e. S )
  assume salpreimagtge.c: |- ( ph -> C e. RR )

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
  assert |- ( ph -> { x e. A | C <_ B } e. S )

  proof
    wph
    cC
    cB
    cle
    wbr
    vx
    cA
    crab
    vn
    cn
    cC
    c1
    vn
    cv
    #
    cdiv
    co
    #
    cmin
    co
    #
    cB
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
    salpreimagtge.x
    salpreimagtge.b
    salpreimagtge.c
    preimageiingt
    wph
    cS
    vn
    @4
    cn
    salpreimagtge.s
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
    wa
    cC
    @1
    wph
    cC
    cr
    wcel
    @5
    salpreimagtge.c
    adantr
    @5
    @1
    cr
    wcel
    wph
    @0
    nnrecre
    adantl
    resubcld
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    #
    @8
    cB
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
    @14
    @7
    va
    wph
    @6
    va
    salpreimagtge.a
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
    cmin
    ovex
    @8
    @2
    wceq
    #
    @10
    @14
    @13
    @7
    @15
    @9
    @6
    wph
    @8
    @2
    cr
    eleq1
    anbi2d
    @15
    @12
    @4
    cS
    @15
    @11
    @3
    vx
    cA
    @8
    @2
    cB
    clt
    breq1
    rabbidv
    eleq1d
    imbi12d
    salpreimagtge.p
    vtoclf
    syldan
    saliincl
    eqeltrd
end
