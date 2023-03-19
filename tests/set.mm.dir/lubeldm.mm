include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "wreu.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "biid.mm"
include "lubdm.mm"
include "eleq2d.mm"
include "wceq.mm"
include "raleq.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "reubidv.mm"
include "reubii.mm"
include "syl6bbr.mm"
include "elrab.mm"
include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "anbi1i.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem lubeldm
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cS: class S
  let cU: class U
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let vs: setvar s
  assume lubeldm.b: |- B = ( Base ` K )
  assume lubeldm.l: |- .<_ = ( le ` K )
  assume lubeldm.u: |- U = ( lub ` K )
  assume lubeldm.p: |- ( ps <-> ( A. y e. S y .<_ x /\ A. z e. B ( A. y e. S y .<_ z -> x .<_ z ) ) )
  assume lubeldm.k: |- ( ph -> K e. V )

  disjoint x z
  disjoint B x
  disjoint B z
  disjoint x y
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint s x
  disjoint s z
  disjoint B s
  disjoint s y
  disjoint K s
  disjoint S s
  disjoint ps s
  assert |- ( ph -> ( S e. dom U <-> ( S C_ B /\ E! x e. B ps ) ) )

  proof
    wph
    cS
    cU
    cdm
    #
    wcel
    cS
    vy
    cv
    #
    vx
    cv
    #
    c.le
    wbr
    #
    vy
    vs
    cv
    #
    wral
    #
    @1
    vz
    cv
    #
    c.le
    wbr
    #
    vy
    @4
    wral
    #
    @2
    @6
    c.le
    wbr
    #
    wi
    #
    vz
    cB
    wral
    #
    wa
    #
    vx
    cB
    wreu
    #
    vs
    cB
    cpw
    #
    crab
    #
    wcel
    #
    cS
    cB
    wss
    #
    wps
    vx
    cB
    wreu
    #
    wa
    #
    wph
    @0
    @15
    cS
    wph
    @12
    vx
    vy
    vz
    cB
    cU
    cK
    c.le
    cV
    vs
    lubeldm.b
    lubeldm.l
    lubeldm.u
    @12
    biid
    lubeldm.k
    lubdm
    eleq2d
    @16
    cS
    @14
    wcel
    #
    @18
    wa
    @19
    @13
    @18
    vs
    cS
    @14
    @4
    cS
    wceq
    #
    @13
    @3
    vy
    cS
    wral
    #
    @7
    vy
    cS
    wral
    #
    @9
    wi
    #
    vz
    cB
    wral
    #
    wa
    #
    vx
    cB
    wreu
    @18
    @21
    @12
    @26
    vx
    cB
    @21
    @5
    @22
    @11
    @25
    @3
    vy
    @4
    cS
    raleq
    @21
    @10
    @24
    vz
    cB
    @21
    @8
    @23
    @9
    @7
    vy
    @4
    cS
    raleq
    imbi1d
    ralbidv
    anbi12d
    reubidv
    wps
    @26
    vx
    cB
    lubeldm.p
    reubii
    syl6bbr
    elrab
    @20
    @17
    @18
    cS
    cB
    cB
    cK
    cbs
    cfv
    cvv
    lubeldm.b
    cK
    cbs
    fvex
    eqeltri
    elpw2
    anbi1i
    bitri
    syl6bb
end
