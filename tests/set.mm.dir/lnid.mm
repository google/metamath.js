include "co.mm"
include "lncgr.mm"
include "eqcomd.mm"
include "axtgcgrid.mm"

theorem lnid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let c.sm: class .~
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tglngval.p: |- P = ( Base ` G )
  assume tglngval.l: |- L = ( LineG ` G )
  assume tglngval.i: |- I = ( Itv ` G )
  assume tglngval.g: |- ( ph -> G e. TarskiG )
  assume tglngval.x: |- ( ph -> X e. P )
  assume tglngval.y: |- ( ph -> Y e. P )
  assume tgcolg.z: |- ( ph -> Z e. P )
  assume lnxfr.r: |- .~ = ( cgrG ` G )
  assume lnxfr.a: |- ( ph -> A e. P )
  assume lnxfr.b: |- ( ph -> B e. P )
  assume lnxfr.d: |- .- = ( dist ` G )
  assume lnid.1: |- ( ph -> X =/= Y )
  assume lnid.2: |- ( ph -> ( Y e. ( X L Z ) \/ X = Z ) )
  assume lnid.3: |- ( ph -> ( X .- Z ) = ( X .- A ) )
  assume lnid.4: |- ( ph -> ( Y .- Z ) = ( Y .- A ) )


  assert |- ( ph -> Z = A )

  proof
    wph
    cP
    cG
    cI
    c.mi
    cZ
    cA
    cZ
    tglngval.p
    lnxfr.d
    tglngval.i
    tglngval.g
    tgcolg.z
    lnxfr.a
    tgcolg.z
    wph
    cZ
    cZ
    c.mi
    co
    cZ
    cA
    c.mi
    co
    wph
    cZ
    cA
    cP
    c.sm
    cG
    cI
    cL
    c.mi
    cX
    cY
    cZ
    tglngval.p
    tglngval.l
    tglngval.i
    tglngval.g
    tglngval.x
    tglngval.y
    tgcolg.z
    lnxfr.r
    tgcolg.z
    lnxfr.a
    lnxfr.d
    lnid.1
    lnid.2
    lnid.3
    lnid.4
    lncgr
    eqcomd
    axtgcgrid
end
