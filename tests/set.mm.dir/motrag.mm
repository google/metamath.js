include "cfv.mm"
include "ccgrg.mm"
include "eqid.mm"
include "cstrkg.mm"
include "motcl.mm"
include "eqidd.mm"
include "motcgr3.mm"
include "ragcgr.mm"

theorem motrag
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cF: class F
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
  assume motrag.f: |- ( ph -> F e. ( G Ismt G ) )
  assume motrag.1: |- ( ph -> <" A B C "> e. ( raG ` G ) )


  assert |- ( ph -> <" ( F ` A ) ( F ` B ) ( F ` C ) "> e. ( raG ` G ) )

  proof
    wph
    cA
    cB
    cC
    cA
    cF
    cfv
    #
    cP
    cG
    ccgrg
    cfv
    #
    cS
    cB
    cF
    cfv
    #
    cC
    cF
    cfv
    #
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
    @1
    eqid
    #
    wph
    cA
    cP
    cF
    cG
    c.mi
    cstrkg
    israg.p
    israg.d
    israg.g
    motrag.f
    israg.a
    motcl
    wph
    cB
    cP
    cF
    cG
    c.mi
    cstrkg
    israg.p
    israg.d
    israg.g
    motrag.f
    israg.b
    motcl
    wph
    cC
    cP
    cF
    cG
    c.mi
    cstrkg
    israg.p
    israg.d
    israg.g
    motrag.f
    israg.c
    motcl
    motrag.1
    wph
    cA
    cB
    cC
    @0
    cP
    @1
    @2
    @3
    cG
    cF
    c.mi
    israg.p
    israg.d
    @4
    israg.g
    israg.a
    israg.b
    israg.c
    wph
    @0
    eqidd
    wph
    @2
    eqidd
    wph
    @3
    eqidd
    motrag.f
    motcgr3
    ragcgr
end
