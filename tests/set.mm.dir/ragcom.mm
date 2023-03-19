include "cs3.mm"
include "crag.mm"
include "cfv.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "mircl.mm"
include "israg.mm"
include "mpbid.mm"
include "tgcgrcomlr.mm"
include "miriso.mm"
include "mirmir.mm"
include "oveq1d.mm"
include "3eqtr2d.mm"
include "mpbird.mm"

theorem ragcom
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
  assume ragcom.1: |- ( ph -> <" A B C "> e. ( raG ` G ) )


  assert |- ( ph -> <" C B A "> e. ( raG ` G ) )

  proof
    wph
    cC
    cB
    cA
    cs3
    cG
    crag
    cfv
    #
    wcel
    cC
    cA
    c.mi
    co
    #
    cC
    cA
    cB
    cS
    cfv
    #
    cfv
    #
    c.mi
    co
    #
    wceq
    wph
    @1
    cC
    @2
    cfv
    #
    cA
    c.mi
    co
    @5
    @2
    cfv
    #
    @3
    c.mi
    co
    @4
    wph
    cA
    cC
    cA
    @5
    cP
    cG
    cI
    c.mi
    israg.p
    israg.d
    israg.i
    israg.g
    israg.a
    israg.c
    israg.a
    wph
    cB
    cP
    cS
    cG
    cI
    cL
    @2
    c.mi
    cC
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    israg.b
    @2
    eqid
    #
    israg.c
    mircl
    #
    wph
    cA
    cB
    cC
    cs3
    @0
    wcel
    cA
    cC
    c.mi
    co
    cA
    @5
    c.mi
    co
    wceq
    ragcom.1
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
    tgcgrcomlr
    wph
    cB
    cP
    cS
    cG
    cI
    cL
    @2
    c.mi
    @5
    cA
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    israg.b
    @7
    @8
    israg.a
    miriso
    wph
    @6
    cC
    @3
    c.mi
    wph
    cB
    cC
    cP
    cS
    cG
    cI
    cL
    @2
    c.mi
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    israg.b
    @7
    israg.c
    mirmir
    oveq1d
    3eqtr2d
    wph
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
    israg.g
    israg.c
    israg.b
    israg.a
    israg
    mpbird
end
