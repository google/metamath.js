include "csalg.mm"
include "wcel.mm"
include "c0.mm"
include "cuni.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "cpw.mm"
include "wa.mm"
include "eqcomi.mm"
include "difeq1i.mm"
include "syl5eqel.mm"
include "ralrimiva.mm"
include "3expia.mm"
include "w3a.mm"
include "wb.mm"
include "issal.mm"
include "syl.mm"
include "mpbir3and.mm"

theorem issald
  let wph: wff ph
  let vy: setvar y
  let cS: class S
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume issald.s: |- ( ph -> S e. V )
  assume issald.z: |- ( ph -> (/) e. S )
  assume issald.x: |- X = U. S
  assume issald.d: |- ( ( ph /\ y e. S ) -> ( X \ y ) e. S )
  assume issald.u: |- ( ( ph /\ y e. ~P S /\ y ~<_ _om ) -> U. y e. S )

  disjoint S y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> S e. SAlg )

  proof
    wph
    cS
    csalg
    wcel
    #
    c0
    cS
    wcel
    #
    cS
    cuni
    #
    vy
    cv
    #
    cdif
    #
    cS
    wcel
    #
    vy
    cS
    wral
    #
    @3
    com
    cdom
    wbr
    #
    @3
    cuni
    cS
    wcel
    #
    wi
    #
    vy
    cS
    cpw
    #
    wral
    #
    issald.z
    wph
    @5
    vy
    cS
    wph
    @3
    cS
    wcel
    wa
    @4
    cX
    @3
    cdif
    cS
    @2
    cX
    @3
    cX
    @2
    issald.x
    eqcomi
    difeq1i
    issald.d
    syl5eqel
    ralrimiva
    wph
    @9
    vy
    @10
    wph
    @3
    @10
    wcel
    @7
    @8
    issald.u
    3expia
    ralrimiva
    wph
    cS
    cV
    wcel
    @0
    @1
    @6
    @11
    w3a
    wb
    issald.s
    vy
    cS
    cV
    issal
    syl
    mpbir3and
end
