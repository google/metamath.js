include "wss.mm"
include "wreu.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "glbeldm.mm"
include "mpbid.mm"
include "simprd.mm"

theorem glbeu
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cS: class S
  let cG: class G
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let vs: setvar s
  assume glbval.b: |- B = ( Base ` K )
  assume glbval.l: |- .<_ = ( le ` K )
  assume glbval.g: |- G = ( glb ` K )
  assume glbval.p: |- ( ps <-> ( A. y e. S x .<_ y /\ A. z e. B ( A. y e. S z .<_ y -> z .<_ x ) ) )
  assume glbva.k: |- ( ph -> K e. V )
  assume glbval.s: |- ( ph -> S e. dom G )

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
    cG
    cdm
    wcel
    @0
    @1
    wa
    glbval.s
    wph
    wps
    vx
    vy
    vz
    cB
    cS
    cG
    cK
    c.le
    cV
    glbval.b
    glbval.l
    glbval.g
    glbval.p
    glbva.k
    glbeldm
    mpbid
    simprd
end
