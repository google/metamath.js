include "cv.mm"
include "cfv.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "crio.mm"
include "wceq.mm"
include "biid.mm"
include "lubelss.mm"
include "lubval.mm"
include "eqcomd.mm"
include "wcel.mm"
include "wreu.mm"
include "wb.mm"
include "lubcl.mm"
include "lubeu.mm"
include "breq2.mm"
include "ralbidv.mm"
include "breq1.mm"
include "imbi2d.mm"
include "anbi12d.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem lubprop
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
  assume lubprop.b: |- B = ( Base ` K )
  assume lubprop.l: |- .<_ = ( le ` K )
  assume lubprop.u: |- U = ( lub ` K )
  assume lubprop.k: |- ( ph -> K e. V )
  assume lubprop.s: |- ( ph -> S e. dom U )

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
  assert |- ( ph -> ( A. y e. S y .<_ ( U ` S ) /\ A. z e. B ( A. y e. S y .<_ z -> ( U ` S ) .<_ z ) ) )

  proof
    wph
    vy
    cv
    #
    cS
    cU
    cfv
    #
    c.le
    wbr
    #
    vy
    cS
    wral
    #
    @0
    vz
    cv
    #
    c.le
    wbr
    vy
    cS
    wral
    #
    @1
    @4
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
    @0
    vx
    cv
    #
    c.le
    wbr
    #
    vy
    cS
    wral
    #
    @5
    @10
    @4
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
    @1
    wceq
    #
    wph
    @1
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
    lubprop.b
    lubprop.l
    lubprop.u
    @16
    biid
    #
    lubprop.k
    wph
    cB
    cS
    cU
    cK
    c.le
    cV
    lubprop.b
    lubprop.l
    lubprop.u
    lubprop.k
    lubprop.s
    lubelss
    lubval
    eqcomd
    wph
    @1
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
    lubprop.b
    lubprop.u
    lubprop.k
    lubprop.s
    lubcl
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
    lubprop.b
    lubprop.l
    lubprop.u
    @19
    lubprop.k
    lubprop.s
    lubeu
    @16
    @9
    vx
    cB
    @1
    @10
    @1
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
    @1
    @0
    c.le
    breq2
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
    @1
    @4
    c.le
    breq1
    imbi2d
    ralbidv
    anbi12d
    riota2
    syl2anc
    mpbird
end
