include "ccgrg.mm"
include "cfv.mm"
include "eqid.mm"
include "ncolrot1.mm"
include "axtgcgrrflx.mm"
include "chlg.mm"
include "cgrane2.mm"
include "ncolne2.mm"
include "necomd.mm"
include "cgraswap.mm"
include "cgracom.mm"
include "cgratr.mm"
include "ncolne1.mm"
include "tgasa.mm"
include "cgr3simp3.mm"

theorem isoas
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  assume isoas.p: |- P = ( Base ` G )
  assume isoas.m: |- .- = ( dist ` G )
  assume isoas.i: |- I = ( Itv ` G )
  assume isoas.l: |- L = ( LineG ` G )
  assume isoas.g: |- ( ph -> G e. TarskiG )
  assume isoas.a: |- ( ph -> A e. P )
  assume isoas.b: |- ( ph -> B e. P )
  assume isoas.c: |- ( ph -> C e. P )
  assume isoas.1: |- ( ph -> -. ( C e. ( A L B ) \/ A = B ) )
  assume isoas.2: |- ( ph -> <" A B C "> ( cgrA ` G ) <" A C B "> )


  assert |- ( ph -> ( A .- B ) = ( A .- C ) )

  proof
    wph
    cB
    cC
    cA
    cC
    cP
    cG
    ccgrg
    cfv
    #
    cB
    cA
    cG
    cI
    c.mi
    isoas.p
    isoas.m
    isoas.i
    @0
    eqid
    isoas.g
    isoas.b
    isoas.c
    isoas.a
    isoas.c
    isoas.b
    isoas.a
    wph
    cB
    cC
    cA
    cC
    cP
    cB
    cA
    cG
    cI
    cL
    c.mi
    isoas.p
    isoas.m
    isoas.i
    isoas.g
    isoas.b
    isoas.c
    isoas.a
    isoas.c
    isoas.b
    isoas.a
    isoas.l
    wph
    cP
    cG
    cI
    cL
    cA
    cB
    cC
    isoas.p
    isoas.l
    isoas.i
    isoas.g
    isoas.a
    isoas.b
    isoas.c
    isoas.1
    ncolrot1
    #
    wph
    cP
    cG
    cI
    c.mi
    cB
    cC
    isoas.p
    isoas.m
    isoas.i
    isoas.g
    isoas.b
    isoas.c
    axtgcgrrflx
    wph
    cB
    cC
    cA
    cA
    cP
    cB
    cB
    cC
    cG
    cC
    cI
    cA
    cG
    chlg
    cfv
    #
    isoas.p
    isoas.i
    isoas.g
    @2
    eqid
    #
    isoas.b
    isoas.c
    isoas.a
    isoas.a
    isoas.b
    isoas.c
    wph
    cB
    cC
    cA
    cA
    cP
    cB
    cC
    cB
    cG
    cA
    cI
    cC
    @2
    isoas.p
    isoas.i
    isoas.g
    @3
    isoas.b
    isoas.c
    isoas.a
    isoas.a
    isoas.c
    isoas.b
    wph
    cB
    cC
    cA
    cP
    cG
    cI
    @2
    isoas.p
    isoas.i
    isoas.g
    @3
    isoas.b
    isoas.c
    isoas.a
    wph
    cA
    cB
    cC
    cA
    cP
    cC
    cB
    cG
    cI
    @2
    isoas.p
    isoas.i
    @3
    isoas.g
    isoas.a
    isoas.b
    isoas.c
    isoas.a
    isoas.c
    isoas.b
    isoas.2
    cgrane2
    #
    wph
    cA
    cC
    wph
    cP
    cG
    cI
    cL
    cA
    cB
    cC
    isoas.p
    isoas.i
    isoas.l
    isoas.g
    isoas.a
    isoas.b
    isoas.c
    @1
    ncolne2
    necomd
    cgraswap
    isoas.a
    isoas.b
    isoas.c
    wph
    cA
    cB
    cC
    cA
    cP
    cC
    cB
    cG
    cI
    @2
    isoas.p
    isoas.i
    isoas.g
    @3
    isoas.a
    isoas.b
    isoas.c
    isoas.a
    isoas.c
    isoas.b
    isoas.2
    cgracom
    cgratr
    isoas.c
    isoas.b
    isoas.a
    wph
    cA
    cB
    cC
    cP
    cG
    cI
    @2
    isoas.p
    isoas.i
    isoas.g
    @3
    isoas.a
    isoas.b
    isoas.c
    wph
    cP
    cG
    cI
    cL
    cA
    cB
    cC
    isoas.p
    isoas.i
    isoas.l
    isoas.g
    isoas.a
    isoas.b
    isoas.c
    @1
    ncolne1
    @4
    cgraswap
    cgratr
    isoas.2
    tgasa
    cgr3simp3
end
