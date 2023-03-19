include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cdm.mm"
include "wcel.mm"
include "wss.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "wreu.mm"
include "ssrab2.mm"
include "a1i.mm"
include "wceq.mm"
include "wb.mm"
include "lublecllem.mm"
include "ralrimiva.mm"
include "reu6i.mm"
include "syl2anc.mm"
include "cpo.mm"
include "biid.mm"
include "lubeldm.mm"
include "mpbir2and.mm"

theorem lublecl
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let cU: class U
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  assume lublecl.b: |- B = ( Base ` K )
  assume lublecl.l: |- .<_ = ( le ` K )
  assume lublecl.u: |- U = ( lub ` K )
  assume lublecl.k: |- ( ph -> K e. Poset )
  assume lublecl.x: |- ( ph -> X e. B )

  disjoint .<_ y
  disjoint B y
  disjoint X y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .<_ w
  disjoint x y
  disjoint x z
  disjoint .<_ x
  disjoint y z
  disjoint .<_ z
  disjoint B w
  disjoint B x
  disjoint B z
  disjoint K w
  disjoint K x
  disjoint K z
  disjoint X w
  disjoint X x
  disjoint X z
  disjoint ph w
  disjoint ph x
  assert |- ( ph -> { y e. B | y .<_ X } e. dom U )

  proof
    wph
    vy
    cv
    cX
    c.le
    wbr
    #
    vy
    cB
    crab
    #
    cU
    cdm
    wcel
    @1
    cB
    wss
    #
    vz
    cv
    #
    vx
    cv
    #
    c.le
    wbr
    vz
    @1
    wral
    @3
    vw
    cv
    #
    c.le
    wbr
    vz
    @1
    wral
    @4
    @5
    c.le
    wbr
    wi
    vw
    cB
    wral
    wa
    #
    vx
    cB
    wreu
    #
    @2
    wph
    @0
    vy
    cB
    ssrab2
    a1i
    wph
    cX
    cB
    wcel
    @6
    @4
    cX
    wceq
    wb
    #
    vx
    cB
    wral
    @7
    lublecl.x
    wph
    @8
    vx
    cB
    wph
    vx
    vy
    vz
    vw
    cB
    cU
    cK
    c.le
    cX
    lublecl.b
    lublecl.l
    lublecl.u
    lublecl.k
    lublecl.x
    lublecllem
    ralrimiva
    @6
    vx
    cB
    cX
    reu6i
    syl2anc
    wph
    @6
    vx
    vz
    vw
    cB
    @1
    cU
    cK
    c.le
    cpo
    lublecl.b
    lublecl.l
    lublecl.u
    @6
    biid
    lublecl.k
    lubeldm
    mpbir2and
end
