include "cc0.mm"
include "cpnf.mm"
include "csu.mm"
include "cxr.mm"
include "wcel.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "cv.mm"
include "wa.mm"
include "cico.mm"
include "co.mm"
include "cr.mm"
include "rge0ssre.mm"
include "sseldi.mm"
include "fsumrecl.mm"
include "rexrd.mm"
include "cle.mm"
include "wbr.mm"
include "icogelb.mm"
include "syl3anc.mm"
include "fsumge0.mm"
include "ltpnfd.mm"
include "elicod.mm"

theorem fsumge0cl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume fsumge0cl.a: |- ( ph -> A e. Fin )
  assume fsumge0cl.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,) +oo ) )

  disjoint A k
  disjoint k ph
  assert |- ( ph -> sum_ k e. A B e. ( 0 [,) +oo ) )

  proof
    wph
    cc0
    cpnf
    cA
    cB
    vk
    csu
    #
    cc0
    cxr
    wcel
    #
    wph
    0xr
    a1i
    cpnf
    cxr
    wcel
    #
    wph
    pnfxr
    a1i
    wph
    @0
    wph
    cA
    cB
    vk
    fsumge0cl.a
    wph
    vk
    cv
    cA
    wcel
    wa
    #
    cc0
    cpnf
    cico
    co
    #
    cr
    cB
    rge0ssre
    fsumge0cl.b
    sseldi
    #
    fsumrecl
    #
    rexrd
    wph
    cA
    cB
    vk
    fsumge0cl.a
    @5
    @3
    @1
    @2
    cB
    @4
    wcel
    cc0
    cB
    cle
    wbr
    @1
    @3
    0xr
    a1i
    @2
    @3
    pnfxr
    a1i
    fsumge0cl.b
    cc0
    cpnf
    cB
    icogelb
    syl3anc
    fsumge0
    wph
    @0
    @6
    ltpnfd
    elicod
end
