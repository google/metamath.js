include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "neneqd.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "cs3.mm"
include "crag.mm"
include "cfv.mm"
include "simpr.mm"
include "ragflat3.mm"
include "mtand.mm"

theorem ragncol
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let vg: setvar g
  let vw: setvar w
  assume israg.p: |- P = ( Base ` G )
  assume israg.d: |- .- = ( dist ` G )
  assume israg.i: |- I = ( Itv ` G )
  assume israg.l: |- L = ( LineG ` G )
  assume israg.s: |- S = ( pInvG ` G )
  assume israg.g: |- ( ph -> G e. TarskiG )
  assume israg.a: |- ( ph -> A e. P )
  assume israg.b: |- ( ph -> B e. P )
  assume israg.c: |- ( ph -> C e. P )
  assume ragncol.1: |- ( ph -> <" A B C "> e. ( raG ` G ) )
  assume ragncol.2: |- ( ph -> A =/= B )
  assume ragncol.3: |- ( ph -> C =/= B )


  assert |- ( ph -> -. ( C e. ( A L B ) \/ A = B ) )

  proof
    wph
    cC
    cA
    cB
    cL
    co
    wcel
    cA
    cB
    wceq
    #
    wo
    #
    @0
    cC
    cB
    wceq
    #
    wo
    #
    wph
    @0
    wn
    @2
    wn
    @3
    wn
    wph
    cA
    cB
    ragncol.2
    neneqd
    wph
    cC
    cB
    ragncol.3
    neneqd
    @0
    @2
    ioran
    sylanbrc
    wph
    @1
    wa
    cA
    cB
    cC
    cP
    cS
    cG
    cI
    cL
    c.mi
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    wph
    cG
    cstrkg
    wcel
    @1
    israg.g
    adantr
    wph
    cA
    cP
    wcel
    @1
    israg.a
    adantr
    wph
    cB
    cP
    wcel
    @1
    israg.b
    adantr
    wph
    cC
    cP
    wcel
    @1
    israg.c
    adantr
    wph
    cA
    cB
    cC
    cs3
    cG
    crag
    cfv
    wcel
    @1
    ragncol.1
    adantr
    wph
    @1
    simpr
    ragflat3
    mtand
end
