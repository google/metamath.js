include "cs3.mm"
include "crag.mm"
include "cfv.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "mircinv.mm"
include "oveq2d.mm"
include "eqcomd.mm"
include "israg.mm"
include "mpbird.mm"

theorem ragtrivb
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


  assert |- ( ph -> <" A B B "> e. ( raG ` G ) )

  proof
    wph
    cA
    cB
    cB
    cs3
    cG
    crag
    cfv
    wcel
    cA
    cB
    c.mi
    co
    #
    cA
    cB
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
    @3
    @0
    wph
    @2
    cB
    cA
    c.mi
    wph
    cB
    cP
    cS
    cG
    cI
    cL
    @1
    c.mi
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    israg.b
    @1
    eqid
    mircinv
    oveq2d
    eqcomd
    wph
    cA
    cB
    cB
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
    israg.b
    israg
    mpbird
end
