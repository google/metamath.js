include "co.mm"
include "cfv.mm"
include "miriso.mm"
include "3eqtr4d.mm"

theorem mircgrs
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cS: class S
  let cT: class T
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
  assume mircgrs.z: |- ( ph -> Z e. P )
  assume mircgrs.t: |- ( ph -> T e. P )
  assume mircgrs.e: |- ( ph -> ( X .- Y ) = ( Z .- T ) )


  assert |- ( ph -> ( ( M ` X ) .- ( M ` Y ) ) = ( ( M ` Z ) .- ( M ` T ) ) )

  proof
    wph
    cX
    cY
    c.mi
    co
    cZ
    cT
    c.mi
    co
    cX
    cM
    cfv
    cY
    cM
    cfv
    c.mi
    co
    cZ
    cM
    cfv
    cT
    cM
    cfv
    c.mi
    co
    mircgrs.e
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
    cT
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirval.a
    mirfv.m
    mircgrs.z
    mircgrs.t
    miriso
    3eqtr4d
end
