include "cv.mm"
include "cico.mm"
include "ccom.mm"
include "cfv.mm"
include "cixp.mm"
include "ciun.mm"
include "cmap.mm"
include "co.mm"
include "cr.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "fvex.mm"
include "rgenw.mm"
include "ixpssmapg.mm"
include "ax-mp.mm"
include "a1i.mm"
include "reex.mm"
include "hoissre.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "mapss.mm"
include "syl2anc.mm"
include "sstrd.mm"

theorem hoissrrn
  let wph: wff ph
  let vk: setvar k
  let cI: class I
  let cX: class X
  let vx: setvar x
  assume hoissrrn.1: |- ( ph -> I : X --> ( RR X. RR ) )

  disjoint X k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> X_ k e. X ( ( [,) o. I ) ` k ) C_ ( RR ^m X ) )

  proof
    wph
    vk
    cX
    vk
    cv
    #
    cico
    cI
    ccom
    #
    cfv
    #
    cixp
    #
    vk
    cX
    @2
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
    @3
    @5
    wss
    #
    wph
    @2
    cvv
    wcel
    #
    vk
    cX
    wral
    @7
    @8
    vk
    cX
    @0
    @1
    fvex
    rgenw
    vk
    cX
    @2
    cvv
    ixpssmapg
    ax-mp
    a1i
    wph
    cr
    cvv
    wcel
    #
    @4
    cr
    wss
    #
    @5
    @6
    wss
    @9
    wph
    reex
    a1i
    wph
    @2
    cr
    wss
    #
    vk
    cX
    wral
    @10
    wph
    @11
    vk
    cX
    wph
    vk
    cI
    cX
    hoissrrn.1
    hoissre
    ralrimiva
    vk
    cX
    @2
    cr
    iunss
    sylibr
    @4
    cr
    cX
    cvv
    mapss
    syl2anc
    sstrd
end
