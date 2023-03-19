include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cr.mm"
include "cfv.mm"
include "rge0ssre.mm"
include "cxr.mm"
include "wcel.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "sstrd.mm"
include "omexrcl.mm"
include "cicc.mm"
include "cle.mm"
include "wbr.mm"
include "omecl.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "rexrd.mm"
include "omessle.mm"
include "ltpnfd.mm"
include "xrlelttrd.mm"
include "elicod.mm"
include "sseldi.mm"

theorem omessre
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cO: class O
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume omessre.o: |- ( ph -> O e. OutMeas )
  assume omessre.x: |- X = U. dom O
  assume omessre.a: |- ( ph -> A C_ X )
  assume omessre.re: |- ( ph -> ( O ` A ) e. RR )
  assume omessre.b: |- ( ph -> B C_ A )


  assert |- ( ph -> ( O ` B ) e. RR )

  proof
    wph
    cc0
    cpnf
    cico
    co
    cr
    cB
    cO
    cfv
    #
    rge0ssre
    wph
    cc0
    cpnf
    @0
    cc0
    cxr
    wcel
    #
    wph
    0xr
    a1i
    #
    cpnf
    cxr
    wcel
    #
    wph
    pnfxr
    a1i
    #
    wph
    cB
    cO
    cX
    omessre.o
    omessre.x
    wph
    cB
    cA
    cX
    omessre.b
    omessre.a
    sstrd
    #
    omexrcl
    #
    wph
    @1
    @3
    @0
    cc0
    cpnf
    cicc
    co
    wcel
    cc0
    @0
    cle
    wbr
    @2
    @4
    wph
    cB
    cO
    cX
    omessre.o
    omessre.x
    @5
    omecl
    cc0
    cpnf
    @0
    iccgelb
    syl3anc
    wph
    @0
    cA
    cO
    cfv
    #
    cpnf
    @6
    wph
    @7
    omessre.re
    rexrd
    @4
    wph
    cB
    cA
    cO
    cX
    omessre.o
    omessre.x
    omessre.a
    omessre.b
    omessle
    wph
    @7
    omessre.re
    ltpnfd
    xrlelttrd
    elicod
    sseldi
end
