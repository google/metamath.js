include "cfv.mm"
include "wceq.mm"
include "ccgrg.mm"
include "eqid.mm"
include "mircl.mm"
include "co.mm"
include "mirbtwn.mm"
include "oveq1d.mm"
include "eleqtrd.mm"
include "tgbtwncom.mm"
include "miriso.mm"
include "mircom.mm"
include "mircgr.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "eqcomd.mm"
include "tgcgrcomlr.mm"
include "3eqtr3rd.mm"
include "tgidinside.mm"
include "mirinv.mm"
include "mpbid.mm"

theorem miduniq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume miduniq.a: |- ( ph -> A e. P )
  assume miduniq.b: |- ( ph -> B e. P )
  assume miduniq.x: |- ( ph -> X e. P )
  assume miduniq.y: |- ( ph -> Y e. P )
  assume miduniq.e: |- ( ph -> ( ( S ` A ) ` X ) = Y )
  assume miduniq.f: |- ( ph -> ( ( S ` B ) ` X ) = Y )


  assert |- ( ph -> A = B )

  proof
    wph
    cB
    cA
    cS
    cfv
    #
    cfv
    #
    cB
    wceq
    cA
    cB
    wceq
    wph
    cB
    @1
    wph
    @1
    cA
    cP
    cG
    ccgrg
    cfv
    #
    cG
    cI
    cL
    c.mi
    cX
    cY
    cB
    mirval.p
    mirval.l
    mirval.i
    mirval.g
    miduniq.x
    miduniq.y
    miduniq.b
    @2
    eqid
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    @0
    c.mi
    cB
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    miduniq.a
    @0
    eqid
    #
    miduniq.b
    mircl
    miduniq.a
    mirval.d
    wph
    cY
    cB
    cX
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    miduniq.y
    miduniq.b
    miduniq.x
    wph
    cB
    cX
    cB
    cS
    cfv
    #
    cfv
    #
    cX
    cI
    co
    cY
    cX
    cI
    co
    wph
    cB
    cX
    cP
    cS
    cG
    cI
    cL
    @4
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    miduniq.b
    @4
    eqid
    #
    miduniq.x
    mirbtwn
    wph
    @5
    cY
    cX
    cI
    miduniq.f
    oveq1d
    eleqtrd
    tgbtwncom
    wph
    cY
    @0
    cfv
    #
    @1
    c.mi
    co
    cY
    cB
    c.mi
    co
    #
    cX
    @1
    c.mi
    co
    cX
    cB
    c.mi
    co
    #
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    @0
    c.mi
    cY
    cB
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    miduniq.a
    @3
    miduniq.y
    miduniq.b
    miriso
    wph
    @7
    cX
    @1
    c.mi
    wph
    cA
    cX
    cY
    cP
    cS
    cG
    cI
    cL
    @0
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    miduniq.a
    @3
    miduniq.x
    miduniq.e
    mircom
    oveq1d
    wph
    cB
    cY
    cB
    cX
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    miduniq.b
    miduniq.y
    miduniq.b
    miduniq.x
    wph
    cB
    cX
    c.mi
    co
    #
    cB
    cY
    c.mi
    co
    #
    wph
    cB
    @5
    c.mi
    co
    @10
    @11
    wph
    cB
    cX
    cP
    cS
    cG
    cI
    cL
    @4
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    miduniq.b
    @6
    miduniq.x
    mircgr
    wph
    @5
    cY
    cB
    c.mi
    miduniq.f
    oveq2d
    eqtr3d
    #
    eqcomd
    tgcgrcomlr
    3eqtr3rd
    wph
    cX
    @0
    cfv
    #
    @1
    c.mi
    co
    @9
    cY
    @1
    c.mi
    co
    @8
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    @0
    c.mi
    cX
    cB
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    miduniq.a
    @3
    miduniq.x
    miduniq.b
    miriso
    wph
    @13
    cY
    @1
    c.mi
    miduniq.e
    oveq1d
    wph
    cB
    cX
    cB
    cY
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    miduniq.b
    miduniq.x
    miduniq.b
    miduniq.y
    @12
    tgcgrcomlr
    3eqtr3rd
    tgidinside
    eqcomd
    wph
    cA
    cB
    cP
    cS
    cG
    cI
    cL
    @0
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    miduniq.a
    @3
    miduniq.b
    mirinv
    mpbid
end
