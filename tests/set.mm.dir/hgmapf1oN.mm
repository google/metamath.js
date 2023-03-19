include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wf1o.mm"
include "hgmapfnN.mm"
include "hgmaprnN.mm"
include "wcel.mm"
include "wa.mm"
include "chlt.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "hgmap11.mm"
include "biimpd.mm"
include "ralrimivva.mm"
include "dff1o6.mm"
include "syl3anbrc.mm"

theorem hgmapf1oN
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume hgmapf1o.h: |- H = ( LHyp ` K )
  assume hgmapf1o.u: |- U = ( ( DVecH ` K ) ` W )
  assume hgmapf1o.r: |- R = ( Scalar ` U )
  assume hgmapf1o.b: |- B = ( Base ` R )
  assume hgmapf1o.g: |- G = ( ( HGMap ` K ) ` W )
  assume hgmapf1o.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> G : B -1-1-onto-> B )

  proof
    wph
    cG
    cB
    wfn
    cG
    crn
    cB
    wceq
    vx
    cv
    #
    cG
    cfv
    vy
    cv
    #
    cG
    cfv
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cB
    wral
    vx
    cB
    wral
    cB
    cB
    cG
    wf1o
    wph
    cB
    cR
    cU
    cG
    cH
    cK
    cW
    hgmapf1o.h
    hgmapf1o.u
    hgmapf1o.r
    hgmapf1o.b
    hgmapf1o.g
    hgmapf1o.k
    hgmapfnN
    wph
    cB
    cR
    cU
    cG
    cH
    cK
    cW
    hgmapf1o.h
    hgmapf1o.u
    hgmapf1o.r
    hgmapf1o.b
    hgmapf1o.g
    hgmapf1o.k
    hgmaprnN
    wph
    @4
    vx
    vy
    cB
    cB
    wph
    @0
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    wa
    #
    wa
    #
    @2
    @3
    @8
    cB
    cR
    cU
    cG
    cH
    cK
    cW
    @0
    @1
    hgmapf1o.h
    hgmapf1o.u
    hgmapf1o.r
    hgmapf1o.b
    hgmapf1o.g
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @7
    hgmapf1o.k
    adantr
    wph
    @5
    @6
    simprl
    wph
    @5
    @6
    simprr
    hgmap11
    biimpd
    ralrimivva
    vx
    vy
    cB
    cB
    cG
    dff1o6
    syl3anbrc
end
