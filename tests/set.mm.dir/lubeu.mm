include "wss.mm"
include "wreu.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "lubeldm.mm"
include "mpbid.mm"
include "simprd.mm"

theorem lubeu
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
  assume lubval.b: |- B = ( Base ` K )
  assume lubval.l: |- .<_ = ( le ` K )
  assume lubval.u: |- U = ( lub ` K )
  assume lubval.p: |- ( ps <-> ( A. y e. S y .<_ x /\ A. z e. B ( A. y e. S y .<_ z -> x .<_ z ) ) )
  assume lubval.k: |- ( ph -> K e. V )
  assume lubeleu.s: |- ( ph -> S e. dom U )

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
  assert |- ( ph -> E! x e. B ps )

  proof
    wph
    cS
    cB
    wss
    #
    wps
    vx
    cB
    wreu
    #
    wph
    cS
    cU
    cdm
    wcel
    @0
    @1
    wa
    lubeleu.s
    wph
    wps
    vx
    vy
    vz
    cB
    cS
    cU
    cK
    c.le
    cV
    lubval.b
    lubval.l
    lubval.u
    lubval.p
    lubval.k
    lubeldm
    mpbid
    simprd
end
