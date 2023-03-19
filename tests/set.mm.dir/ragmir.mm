include "cfv.mm"
include "cs3.mm"
include "crag.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "mirmir.mm"
include "oveq2d.mm"
include "israg.mm"
include "mpbid.mm"
include "eqtr2d.mm"
include "mircl.mm"
include "mpbird.mm"

theorem ragmir
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
  assume ragmir.1: |- ( ph -> <" A B C "> e. ( raG ` G ) )


  assert |- ( ph -> <" A B ( ( S ` B ) ` C ) "> e. ( raG ` G ) )

  proof
    wph
    cA
    cB
    cC
    cB
    cS
    cfv
    #
    cfv
    #
    cs3
    cG
    crag
    cfv
    #
    wcel
    cA
    @1
    c.mi
    co
    #
    cA
    @1
    @0
    cfv
    #
    c.mi
    co
    #
    wceq
    wph
    @5
    cA
    cC
    c.mi
    co
    #
    @3
    wph
    @4
    cC
    cA
    c.mi
    wph
    cB
    cC
    cP
    cS
    cG
    cI
    cL
    @0
    c.mi
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    israg.b
    @0
    eqid
    #
    israg.c
    mirmir
    oveq2d
    wph
    cA
    cB
    cC
    cs3
    @2
    wcel
    @6
    @3
    wceq
    ragmir.1
    wph
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
    israg.g
    israg.a
    israg.b
    israg.c
    israg
    mpbid
    eqtr2d
    wph
    cA
    cB
    @1
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
    israg.g
    israg.a
    israg.b
    wph
    cB
    cP
    cS
    cG
    cI
    cL
    @0
    c.mi
    cC
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    israg.b
    @7
    israg.c
    mircl
    israg
    mpbird
end
