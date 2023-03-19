include "crn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wne.mm"
include "wfal.mm"
include "cbs.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "ad4antr.mm"
include "simpllr.mm"
include "simplr.mm"
include "tgldim0eq.mm"
include "simprr.mm"
include "pm2.21ddne.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "tgisline.mm"
include "r19.29vva.mm"
include "inegd.mm"

theorem tglndim0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cG: class G
  let cI: class I
  let cL: class L
  let vx: setvar x
  let vy: setvar y
  assume tglineelsb2.p: |- B = ( Base ` G )
  assume tglineelsb2.i: |- I = ( Itv ` G )
  assume tglineelsb2.l: |- L = ( LineG ` G )
  assume tglineelsb2.g: |- ( ph -> G e. TarskiG )
  assume tglndim0.d: |- ( ph -> ( # ` B ) = 1 )


  assert |- ( ph -> -. A e. ran L )

  proof
    wph
    cA
    cL
    crn
    wcel
    #
    wph
    @0
    wa
    #
    cA
    vx
    cv
    #
    vy
    cv
    #
    cL
    co
    wceq
    #
    @2
    @3
    wne
    #
    wa
    #
    wfal
    vx
    vy
    cB
    cB
    @1
    @2
    cB
    wcel
    #
    wa
    #
    @3
    cB
    wcel
    #
    wa
    #
    @6
    wa
    #
    wfal
    @2
    @3
    @11
    @2
    @3
    cB
    cbs
    cG
    tglineelsb2.p
    wph
    cB
    chash
    cfv
    c1
    wceq
    @0
    @7
    @9
    @6
    tglndim0.d
    ad4antr
    @1
    @7
    @9
    @6
    simpllr
    @8
    @9
    @6
    simplr
    tgldim0eq
    @10
    @4
    @5
    simprr
    pm2.21ddne
    @1
    vx
    vy
    cA
    cB
    cG
    cI
    cL
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    wph
    cG
    cstrkg
    wcel
    @0
    tglineelsb2.g
    adantr
    wph
    @0
    simpr
    tgisline
    r19.29vva
    inegd
end
