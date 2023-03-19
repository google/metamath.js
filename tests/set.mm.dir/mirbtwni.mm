include "cfv.mm"
include "ccgrg.mm"
include "eqid.mm"
include "mirf.mm"
include "ffvelrnd.mm"
include "co.mm"
include "miriso.mm"
include "eqcomd.mm"
include "trgcgr.mm"
include "tgbtwnxfr.mm"

theorem mirbtwni
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
  let cZ: class Z
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
  assume mirbtwni.z: |- ( ph -> Z e. P )
  assume mirbtwni.b: |- ( ph -> Y e. ( X I Z ) )


  assert |- ( ph -> ( M ` Y ) e. ( ( M ` X ) I ( M ` Z ) ) )

  proof
    wph
    cX
    cY
    cZ
    cX
    cM
    cfv
    #
    cP
    cG
    ccgrg
    cfv
    #
    cY
    cM
    cfv
    #
    cZ
    cM
    cfv
    #
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    @1
    eqid
    #
    mirval.g
    miriso.1
    miriso.2
    mirbtwni.z
    wph
    cP
    cP
    cX
    cM
    wph
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
    mirval.a
    mirfv.m
    mirf
    #
    miriso.1
    ffvelrnd
    #
    wph
    cP
    cP
    cY
    cM
    @5
    miriso.2
    ffvelrnd
    #
    wph
    cP
    cP
    cZ
    cM
    @5
    mirbtwni.z
    ffvelrnd
    #
    wph
    cX
    cY
    cZ
    @0
    cP
    @1
    @2
    @3
    cG
    c.mi
    mirval.p
    mirval.d
    @4
    mirval.g
    miriso.1
    miriso.2
    mirbtwni.z
    @6
    @7
    @8
    wph
    @0
    @2
    c.mi
    co
    cX
    cY
    c.mi
    co
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
    cY
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirval.a
    mirfv.m
    miriso.1
    miriso.2
    miriso
    eqcomd
    wph
    @2
    @3
    c.mi
    co
    cY
    cZ
    c.mi
    co
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
    cZ
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirval.a
    mirfv.m
    miriso.2
    mirbtwni.z
    miriso
    eqcomd
    wph
    @3
    @0
    c.mi
    co
    cZ
    cX
    c.mi
    co
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cZ
    cX
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirval.a
    mirfv.m
    mirbtwni.z
    miriso.1
    miriso
    eqcomd
    trgcgr
    mirbtwni.b
    tgbtwnxfr
end
