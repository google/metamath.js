include "cfv.mm"
include "mircl.mm"
include "co.mm"
include "cgr3simp1.mm"
include "tgcgrcomlr.mm"
include "mircgr.mm"
include "3eqtr4d.mm"
include "cgr3simp2.mm"
include "mirbtwn.mm"
include "btwncolg1.mm"
include "colcom.mm"
include "mircgrextend.mm"
include "trgcgr.mm"
include "cgr3simp3.mm"
include "tgfscgr.mm"

theorem mirtrcgr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.sm: class .~
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume mirtrcgr.e: |- .~ = ( cgrG ` G )
  assume mirtrcgr.m: |- M = ( S ` B )
  assume mirtrcgr.n: |- N = ( S ` Y )
  assume mirtrcgr.a: |- ( ph -> A e. P )
  assume mirtrcgr.b: |- ( ph -> B e. P )
  assume mirtrcgr.x: |- ( ph -> X e. P )
  assume mirtrcgr.y: |- ( ph -> Y e. P )
  assume mirtrcgr.c: |- ( ph -> C e. P )
  assume mirtrcgr.z: |- ( ph -> Z e. P )
  assume mirtrcgr.1: |- ( ph -> A =/= B )
  assume mirtrcgr.2: |- ( ph -> <" A B C "> .~ <" X Y Z "> )


  assert |- ( ph -> <" ( M ` A ) B C "> .~ <" ( N ` X ) Y Z "> )

  proof
    wph
    cA
    cM
    cfv
    #
    cB
    cC
    cX
    cN
    cfv
    #
    cP
    c.sm
    cY
    cZ
    cG
    c.mi
    mirval.p
    mirval.d
    mirtrcgr.e
    mirval.g
    wph
    cB
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cA
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirtrcgr.b
    mirtrcgr.m
    mirtrcgr.a
    mircl
    #
    mirtrcgr.b
    mirtrcgr.c
    wph
    cY
    cP
    cS
    cG
    cI
    cL
    cN
    c.mi
    cX
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirtrcgr.y
    mirtrcgr.n
    mirtrcgr.x
    mircl
    #
    mirtrcgr.y
    mirtrcgr.z
    wph
    cB
    @0
    cY
    @1
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    mirtrcgr.b
    @2
    mirtrcgr.y
    @3
    wph
    cB
    cA
    c.mi
    co
    cY
    cX
    c.mi
    co
    cB
    @0
    c.mi
    co
    cY
    @1
    c.mi
    co
    wph
    cA
    cB
    cX
    cY
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    mirtrcgr.a
    mirtrcgr.b
    mirtrcgr.x
    mirtrcgr.y
    wph
    cA
    cB
    cC
    cX
    cP
    c.sm
    cY
    cZ
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirtrcgr.e
    mirval.g
    mirtrcgr.a
    mirtrcgr.b
    mirtrcgr.c
    mirtrcgr.x
    mirtrcgr.y
    mirtrcgr.z
    mirtrcgr.2
    cgr3simp1
    #
    tgcgrcomlr
    wph
    cB
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirtrcgr.b
    mirtrcgr.m
    mirtrcgr.a
    mircgr
    wph
    cY
    cX
    cP
    cS
    cG
    cI
    cL
    cN
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirtrcgr.y
    mirtrcgr.n
    mirtrcgr.x
    mircgr
    3eqtr4d
    #
    tgcgrcomlr
    wph
    cA
    cB
    cC
    cX
    cP
    c.sm
    cY
    cZ
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirtrcgr.e
    mirval.g
    mirtrcgr.a
    mirtrcgr.b
    mirtrcgr.c
    mirtrcgr.x
    mirtrcgr.y
    mirtrcgr.z
    mirtrcgr.2
    cgr3simp2
    #
    wph
    @0
    cC
    @1
    cZ
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    @2
    mirtrcgr.c
    @3
    mirtrcgr.z
    wph
    cX
    cY
    @1
    cZ
    cP
    c.sm
    cC
    cG
    cI
    cL
    c.mi
    cA
    cB
    @0
    mirval.p
    mirval.l
    mirval.i
    mirval.g
    mirtrcgr.a
    mirtrcgr.b
    @2
    mirtrcgr.e
    mirtrcgr.x
    mirtrcgr.y
    mirval.d
    mirtrcgr.c
    @3
    mirtrcgr.z
    wph
    cP
    cG
    cI
    cL
    @0
    cA
    cB
    mirval.p
    mirval.l
    mirval.i
    mirval.g
    @2
    mirtrcgr.a
    mirtrcgr.b
    wph
    cP
    cG
    cI
    cL
    @0
    cA
    cB
    mirval.p
    mirval.l
    mirval.i
    mirval.g
    @2
    mirtrcgr.a
    mirtrcgr.b
    wph
    cB
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirtrcgr.b
    mirtrcgr.m
    mirtrcgr.a
    mirbtwn
    btwncolg1
    colcom
    wph
    cA
    cB
    @0
    cX
    cP
    c.sm
    cY
    @1
    cG
    c.mi
    mirval.p
    mirval.d
    mirtrcgr.e
    mirval.g
    mirtrcgr.a
    mirtrcgr.b
    @2
    mirtrcgr.x
    mirtrcgr.y
    @3
    @4
    @5
    wph
    cA
    @0
    cX
    @1
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    mirtrcgr.a
    @2
    mirtrcgr.x
    @3
    wph
    cA
    cB
    cP
    c.sm
    cS
    cG
    cI
    cL
    cM
    c.mi
    cN
    cX
    cY
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirtrcgr.e
    mirtrcgr.m
    mirtrcgr.n
    mirtrcgr.a
    mirtrcgr.b
    mirtrcgr.x
    mirtrcgr.y
    @4
    mircgrextend
    tgcgrcomlr
    trgcgr
    wph
    cC
    cA
    cZ
    cX
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    mirtrcgr.c
    mirtrcgr.a
    mirtrcgr.z
    mirtrcgr.x
    wph
    cA
    cB
    cC
    cX
    cP
    c.sm
    cY
    cZ
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirtrcgr.e
    mirval.g
    mirtrcgr.a
    mirtrcgr.b
    mirtrcgr.c
    mirtrcgr.x
    mirtrcgr.y
    mirtrcgr.z
    mirtrcgr.2
    cgr3simp3
    tgcgrcomlr
    @6
    mirtrcgr.1
    tgfscgr
    tgcgrcomlr
    trgcgr
end
