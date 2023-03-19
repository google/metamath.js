include "cfv.mm"
include "mircl.mm"
include "eqid.mm"
include "mircgr.mm"
include "mircgrs.mm"
include "mirbtwn.mm"
include "mirbtwni.mm"
include "ismir.mm"

theorem mirmir2
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let vg: setvar g
  let va: setvar a
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume mirval.a: |- ( ph -> A e. P )
  assume mirfv.m: |- M = ( S ` A )
  assume miriso.1: |- ( ph -> X e. P )
  assume miriso.2: |- ( ph -> Y e. P )


  assert |- ( ph -> ( M ` ( ( S ` Y ) ` X ) ) = ( ( S ` ( M ` Y ) ) ` ( M ` X ) ) )

  proof
    wph
    cY
    cM
    cfv
    #
    cX
    cM
    cfv
    cX
    cY
    cS
    cfv
    #
    cfv
    #
    cM
    cfv
    cP
    cS
    cG
    cI
    cL
    @0
    cS
    cfv
    #
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cY
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirval.a
    mirfv.m
    miriso.2
    mircl
    @3
    eqid
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cX
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirval.a
    mirfv.m
    miriso.1
    mircl
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    @2
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirval.a
    mirfv.m
    wph
    cY
    cP
    cS
    cG
    cI
    cL
    @1
    c.mi
    cX
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    miriso.2
    @1
    eqid
    #
    miriso.1
    mircl
    #
    mircl
    wph
    cA
    cP
    cS
    cX
    cG
    cI
    cL
    cM
    c.mi
    cY
    @2
    cY
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirval.a
    mirfv.m
    miriso.2
    @5
    miriso.2
    miriso.1
    wph
    cY
    cX
    cP
    cS
    cG
    cI
    cL
    @1
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    miriso.2
    @4
    miriso.1
    mircgr
    mircgrs
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    @2
    cY
    cX
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirval.a
    mirfv.m
    @5
    miriso.2
    miriso.1
    wph
    cY
    cX
    cP
    cS
    cG
    cI
    cL
    @1
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    miriso.2
    @4
    miriso.1
    mirbtwn
    mirbtwni
    ismir
end
