include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "clo1.mm"
include "cneg.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "cicc.mm"
include "co.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "adantr.mm"
include "mpbid.mm"
include "simp3d.mm"
include "ello1d.mm"
include "renegcld.mm"
include "simp2d.mm"
include "adantrr.mm"
include "lenegd.mm"
include "o1lo1.mm"
include "mpbir2and.mm"

theorem icco1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  let cN: class N
  assume icco1.1: |- ( ph -> A C_ RR )
  assume icco1.2: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume icco1.3: |- ( ph -> C e. RR )
  assume icco1.4: |- ( ph -> M e. RR )
  assume icco1.5: |- ( ph -> N e. RR )
  assume icco1.6: |- ( ( ph /\ ( x e. A /\ C <_ x ) ) -> B e. ( M [,] N ) )

  disjoint A x
  disjoint C x
  disjoint M x
  disjoint N x
  disjoint ph x
  assert |- ( ph -> ( x e. A |-> B ) e. O(1) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    co1
    wcel
    @0
    clo1
    wcel
    vx
    cA
    cB
    cneg
    #
    cmpt
    clo1
    wcel
    wph
    vx
    cA
    cB
    cC
    cN
    icco1.1
    icco1.2
    icco1.3
    icco1.5
    wph
    vx
    cv
    #
    cA
    wcel
    #
    cC
    @2
    cle
    wbr
    #
    wa
    #
    wa
    #
    cB
    cr
    wcel
    #
    cM
    cB
    cle
    wbr
    #
    cB
    cN
    cle
    wbr
    #
    @6
    cB
    cM
    cN
    cicc
    co
    wcel
    #
    @7
    @8
    @9
    w3a
    #
    icco1.6
    wph
    @10
    @11
    wb
    #
    @5
    wph
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    @12
    icco1.4
    icco1.5
    cM
    cN
    cB
    elicc2
    syl2anc
    adantr
    mpbid
    #
    simp3d
    ello1d
    wph
    vx
    cA
    @1
    cC
    cM
    cneg
    #
    icco1.1
    wph
    @3
    wa
    cB
    icco1.2
    renegcld
    icco1.3
    wph
    cM
    icco1.4
    renegcld
    @6
    @8
    @1
    @15
    cle
    wbr
    @6
    @7
    @8
    @9
    @14
    simp2d
    @6
    cM
    cB
    wph
    @13
    @5
    icco1.4
    adantr
    wph
    @3
    @7
    @4
    icco1.2
    adantrr
    lenegd
    mpbid
    ello1d
    wph
    vx
    cA
    cB
    icco1.2
    o1lo1
    mpbir2and
end
