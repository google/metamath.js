include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "wne.mm"
include "cr.mm"
include "cxr.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "pnfxr.mm"
include "a1i.mm"
include "rexrd.mm"
include "ltpnfd.mm"
include "xrlelttrd.mm"
include "xrltned.mm"
include "ge0xrre.mm"
include "syl2anc.mm"

theorem ge0lere
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ge0lere.a: |- ( ph -> A e. RR )
  assume ge0lere.b: |- ( ph -> B e. ( 0 [,] +oo ) )
  assume ge0lere.l: |- ( ph -> B <_ A )


  assert |- ( ph -> B e. RR )

  proof
    wph
    cB
    cc0
    cpnf
    cicc
    co
    #
    wcel
    cB
    cpnf
    wne
    cB
    cr
    wcel
    ge0lere.b
    wph
    cB
    cpnf
    wph
    @0
    cxr
    cB
    cc0
    cpnf
    iccssxr
    ge0lere.b
    sseldi
    #
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    #
    wph
    cB
    cA
    cpnf
    @1
    wph
    cA
    ge0lere.a
    rexrd
    @2
    ge0lere.l
    wph
    cA
    ge0lere.a
    ltpnfd
    xrlelttrd
    xrltned
    cB
    ge0xrre
    syl2anc
end
