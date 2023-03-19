include "cfv.mm"
include "mircl.mm"
include "mirbtwn.mm"
include "tgbtwncom.mm"
include "co.mm"
include "tgcgrcomlr.mm"
include "mircgr.mm"
include "3eqtr4d.mm"
include "tgcgrextend.mm"

theorem mircgrextend
  let wph: wff ph
  let cA: class A
  let cB: class B
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
  assume mircgrextend.1: |- ( ph -> ( A .- B ) = ( X .- Y ) )


  assert |- ( ph -> ( A .- ( M ` A ) ) = ( X .- ( N ` X ) ) )

  proof
    wph
    cA
    cB
    cA
    cM
    cfv
    #
    cX
    cP
    cY
    cX
    cN
    cfv
    #
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    mirtrcgr.a
    mirtrcgr.b
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
    mirtrcgr.x
    mirtrcgr.y
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
    wph
    @0
    cB
    cA
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    @2
    mirtrcgr.b
    mirtrcgr.a
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
    tgbtwncom
    wph
    @1
    cY
    cX
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    @3
    mirtrcgr.y
    mirtrcgr.x
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
    mirbtwn
    tgbtwncom
    mircgrextend.1
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
    mircgrextend.1
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
    tgcgrextend
end
