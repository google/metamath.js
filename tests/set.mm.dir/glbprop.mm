include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "crio.mm"
include "wceq.mm"
include "biid.mm"
include "glbelss.mm"
include "glbval.mm"
include "eqcomd.mm"
include "wcel.mm"
include "wreu.mm"
include "wb.mm"
include "glbcl.mm"
include "glbeu.mm"
include "breq1.mm"
include "ralbidv.mm"
include "breq2.mm"
include "imbi2d.mm"
include "anbi12d.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem glbprop
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cS: class S
  let cU: class U
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let vx: setvar x
  let cX: class X
  assume glbprop.b: |- B = ( Base ` K )
  assume glbprop.l: |- .<_ = ( le ` K )
  assume glbprop.u: |- U = ( glb ` K )
  assume glbprop.k: |- ( ph -> K e. V )
  assume glbprop.s: |- ( ph -> S e. dom U )

  disjoint B z
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint S y
  disjoint S z
  disjoint .<_ y
  disjoint U y
  disjoint U z
  disjoint x z
  disjoint B x
  disjoint x y
  disjoint K x
  disjoint S x
  disjoint .<_ x
  disjoint U x
  disjoint X y
  assert |- ( ph -> ( A. y e. S ( U ` S ) .<_ y /\ A. z e. B ( A. y e. S z .<_ y -> z .<_ ( U ` S ) ) ) )

  proof
    wph
    cS
    cU
    cfv
    #
    vy
    cv
    #
    c.le
    wbr
    #
    vy
    cS
    wral
    #
    vz
    cv
    #
    @1
    c.le
    wbr
    vy
    cS
    wral
    #
    @4
    @0
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
    cv
    #
    @1
    c.le
    wbr
    #
    vy
    cS
    wral
    #
    @5
    @4
    @10
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
    crio
    #
    @0
    wceq
    #
    wph
    @0
    @17
    wph
    @16
    vx
    vy
    vz
    cB
    cS
    cU
    cK
    c.le
    cV
    glbprop.b
    glbprop.l
    glbprop.u
    @16
    biid
    #
    glbprop.k
    wph
    cB
    cS
    cU
    cK
    c.le
    cV
    glbprop.b
    glbprop.l
    glbprop.u
    glbprop.k
    glbprop.s
    glbelss
    glbval
    eqcomd
    wph
    @0
    cB
    wcel
    @16
    vx
    cB
    wreu
    @9
    @18
    wb
    wph
    cB
    cS
    cU
    cK
    cV
    glbprop.b
    glbprop.u
    glbprop.k
    glbprop.s
    glbcl
    wph
    @16
    vx
    vy
    vz
    cB
    cS
    cU
    cK
    c.le
    cV
    glbprop.b
    glbprop.l
    glbprop.u
    @19
    glbprop.k
    glbprop.s
    glbeu
    @16
    @9
    vx
    cB
    @0
    @10
    @0
    wceq
    #
    @12
    @3
    @15
    @8
    @20
    @11
    @2
    vy
    cS
    @10
    @0
    @1
    c.le
    breq1
    ralbidv
    @20
    @14
    @7
    vz
    cB
    @20
    @13
    @6
    @5
    @10
    @0
    @4
    c.le
    breq2
    imbi2d
    ralbidv
    anbi12d
    riota2
    syl2anc
    mpbird
end
