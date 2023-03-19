include "wceq.mm"
include "wn.mm"
include "wa.mm"
include "cstrkg.mm"
include "wcel.mm"
include "adantr.mm"
include "cs3.mm"
include "crag.mm"
include "cfv.mm"
include "simpr.mm"
include "neqned.mm"
include "co.mm"
include "wo.mm"
include "colrot1.mm"
include "ragcol.mm"
include "ragtriva.mm"
include "ex.mm"
include "orrd.mm"

theorem ragflat3
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
  assume ragflat3.1: |- ( ph -> <" A B C "> e. ( raG ` G ) )
  assume ragflat3.2: |- ( ph -> ( C e. ( A L B ) \/ A = B ) )


  assert |- ( ph -> ( A = B \/ C = B ) )

  proof
    wph
    cA
    cB
    wceq
    #
    cC
    cB
    wceq
    #
    wph
    @0
    wn
    #
    @1
    wph
    @2
    wa
    #
    cC
    cB
    cA
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
    @2
    israg.g
    adantr
    #
    wph
    cC
    cP
    wcel
    @2
    israg.c
    adantr
    #
    wph
    cB
    cP
    wcel
    @2
    israg.b
    adantr
    #
    wph
    cA
    cP
    wcel
    @2
    israg.a
    adantr
    #
    @3
    cA
    cB
    cC
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
    @4
    @7
    @6
    @5
    @5
    wph
    cA
    cB
    cC
    cs3
    cG
    crag
    cfv
    wcel
    @2
    ragflat3.1
    adantr
    @3
    cA
    cB
    wph
    @2
    simpr
    neqned
    @3
    cP
    cG
    cI
    cL
    cA
    cB
    cC
    israg.p
    israg.l
    israg.i
    @4
    @7
    @6
    @5
    wph
    cC
    cA
    cB
    cL
    co
    wcel
    @0
    wo
    @2
    ragflat3.2
    adantr
    colrot1
    ragcol
    ragtriva
    ex
    orrd
end
