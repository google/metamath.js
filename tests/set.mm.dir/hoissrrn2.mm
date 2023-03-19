include "cico.mm"
include "co.mm"
include "cixp.mm"
include "ciun.mm"
include "cmap.mm"
include "cr.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "ovex.mm"
include "rgenw.mm"
include "ixpssmapg.mm"
include "ax-mp.mm"
include "a1i.mm"
include "reex.mm"
include "cv.mm"
include "wa.mm"
include "cxr.mm"
include "icossre.mm"
include "syl2anc.mm"
include "ex.mm"
include "ralrimi.mm"
include "iunss.mm"
include "sylibr.mm"
include "mapss.mm"
include "sstrd.mm"

theorem hoissrrn2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cX: class X
  let vx: setvar x
  assume hoissrrn2.kph: |- F/ k ph
  assume hoissrrn2.a: |- ( ( ph /\ k e. X ) -> A e. RR )
  assume hoissrrn2.b: |- ( ( ph /\ k e. X ) -> B e. RR* )

  disjoint X k
  disjoint k x
  assert |- ( ph -> X_ k e. X ( A [,) B ) C_ ( RR ^m X ) )

  proof
    wph
    vk
    cX
    cA
    cB
    cico
    co
    #
    cixp
    #
    vk
    cX
    @0
    ciun
    #
    cX
    cmap
    co
    #
    cr
    cX
    cmap
    co
    #
    @1
    @3
    wss
    #
    wph
    @0
    cvv
    wcel
    #
    vk
    cX
    wral
    @5
    @6
    vk
    cX
    cA
    cB
    cico
    ovex
    rgenw
    vk
    cX
    @0
    cvv
    ixpssmapg
    ax-mp
    a1i
    wph
    cr
    cvv
    wcel
    #
    @2
    cr
    wss
    #
    @3
    @4
    wss
    @7
    wph
    reex
    a1i
    wph
    @0
    cr
    wss
    #
    vk
    cX
    wral
    @8
    wph
    @9
    vk
    cX
    hoissrrn2.kph
    wph
    vk
    cv
    cX
    wcel
    #
    @9
    wph
    @10
    wa
    cA
    cr
    wcel
    cB
    cxr
    wcel
    @9
    hoissrrn2.a
    hoissrrn2.b
    cA
    cB
    icossre
    syl2anc
    ex
    ralrimi
    vk
    cX
    @0
    cr
    iunss
    sylibr
    @2
    cr
    cX
    cvv
    mapss
    syl2anc
    sstrd
end
