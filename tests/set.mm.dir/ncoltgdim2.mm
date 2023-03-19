include "c2.mm"
include "cstrkgld.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "tgdim01ln.mm"
include "mtand.mm"
include "notnotrd.mm"

theorem ncoltgdim2
  let wph: wff ph
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
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
  assume ncoltgdim2.1: |- ( ph -> -. ( Z e. ( X L Y ) \/ X = Y ) )


  assert |- ( ph -> G TarskiGDim>= 2 )

  proof
    wph
    cG
    c2
    cstrkgld
    wbr
    #
    wph
    @0
    wn
    #
    cZ
    cX
    cY
    cL
    co
    wcel
    cX
    cY
    wceq
    wo
    ncoltgdim2.1
    wph
    @1
    wa
    cP
    cG
    cI
    cL
    cX
    cY
    cZ
    tglngval.p
    tglngval.l
    tglngval.i
    wph
    cG
    cstrkg
    wcel
    @1
    tglngval.g
    adantr
    wph
    cX
    cP
    wcel
    @1
    tglngval.x
    adantr
    wph
    cY
    cP
    wcel
    @1
    tglngval.y
    adantr
    wph
    cZ
    cP
    wcel
    @1
    tgcolg.z
    adantr
    wph
    @1
    simpr
    tgdim01ln
    mtand
    notnotrd
end
