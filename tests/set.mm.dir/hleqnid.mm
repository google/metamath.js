include "cfv.mm"
include "wbr.mm"
include "wne.mm"
include "wn.mm"
include "neirr.mm"
include "a1i.mm"
include "wa.mm"
include "cstrkg.mm"
include "wcel.mm"
include "adantr.mm"
include "simpr.mm"
include "hlne1.mm"
include "mtand.mm"

theorem hleqnid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cG: class G
  let cI: class I
  let cK: class K
  assume ishlg.p: |- P = ( Base ` G )
  assume ishlg.i: |- I = ( Itv ` G )
  assume ishlg.k: |- K = ( hlG ` G )
  assume ishlg.a: |- ( ph -> A e. P )
  assume ishlg.b: |- ( ph -> B e. P )
  assume ishlg.c: |- ( ph -> C e. P )
  assume hlln.1: |- ( ph -> G e. TarskiG )


  assert |- ( ph -> -. A ( K ` A ) B )

  proof
    wph
    cA
    cB
    cA
    cK
    cfv
    wbr
    #
    cA
    cA
    wne
    #
    @1
    wn
    wph
    cA
    neirr
    a1i
    wph
    @0
    wa
    cA
    cB
    cA
    cP
    cG
    cI
    cK
    cstrkg
    ishlg.p
    ishlg.i
    ishlg.k
    wph
    cA
    cP
    wcel
    @0
    ishlg.a
    adantr
    #
    wph
    cB
    cP
    wcel
    @0
    ishlg.b
    adantr
    @2
    wph
    cG
    cstrkg
    wcel
    @0
    hlln.1
    adantr
    wph
    @0
    simpr
    hlne1
    mtand
end
