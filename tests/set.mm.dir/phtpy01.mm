include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "co.mm"
include "cicc.mm"
include "wcel.mm"
include "wa.mm"
include "1elunit.mm"
include "phtpyi.mm"
include "mpan2.mm"
include "simpld.mm"
include "0elunit.mm"
include "cii.mm"
include "ctopon.mm"
include "iitopon.mm"
include "a1i.mm"
include "cphtpy.mm"
include "chtpy.mm"
include "phtpyhtpy.mm"
include "sseldd.mm"
include "htpyi.mm"
include "simprd.mm"
include "eqtr3d.mm"
include "jca.mm"

theorem phtpy01
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cA: class A
  let vs: setvar s
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  let vj: setvar j
  assume isphtpy.2: |- ( ph -> F e. ( II Cn J ) )
  assume isphtpy.3: |- ( ph -> G e. ( II Cn J ) )
  assume phtpyi.1: |- ( ph -> H e. ( F ( PHtpy ` J ) G ) )


  assert |- ( ph -> ( ( F ` 0 ) = ( G ` 0 ) /\ ( F ` 1 ) = ( G ` 1 ) ) )

  proof
    wph
    cc0
    cF
    cfv
    #
    cc0
    cG
    cfv
    #
    wceq
    c1
    cF
    cfv
    #
    c1
    cG
    cfv
    #
    wceq
    wph
    cc0
    c1
    cH
    co
    #
    @0
    @1
    wph
    @4
    @0
    wceq
    #
    c1
    c1
    cH
    co
    #
    @2
    wceq
    #
    wph
    c1
    cc0
    c1
    cicc
    co
    #
    wcel
    #
    @5
    @7
    wa
    1elunit
    wph
    c1
    cF
    cG
    cH
    cJ
    isphtpy.2
    isphtpy.3
    phtpyi.1
    phtpyi
    mpan2
    #
    simpld
    wph
    cc0
    cc0
    cH
    co
    @0
    wceq
    #
    @4
    @1
    wceq
    #
    wph
    cc0
    @8
    wcel
    @11
    @12
    wa
    0elunit
    wph
    cc0
    cF
    cG
    cH
    cii
    cJ
    @8
    cii
    @8
    ctopon
    cfv
    wcel
    wph
    iitopon
    a1i
    #
    isphtpy.2
    isphtpy.3
    wph
    cF
    cG
    cJ
    cphtpy
    cfv
    co
    cF
    cG
    cii
    cJ
    chtpy
    co
    co
    cH
    wph
    cF
    cG
    cJ
    isphtpy.2
    isphtpy.3
    phtpyhtpy
    phtpyi.1
    sseldd
    #
    htpyi
    mpan2
    simprd
    eqtr3d
    wph
    @6
    @2
    @3
    wph
    @5
    @7
    @10
    simprd
    wph
    c1
    cc0
    cH
    co
    @2
    wceq
    #
    @6
    @3
    wceq
    #
    wph
    @9
    @15
    @16
    wa
    1elunit
    wph
    c1
    cF
    cG
    cH
    cii
    cJ
    @8
    @13
    isphtpy.2
    isphtpy.3
    @14
    htpyi
    mpan2
    simprd
    eqtr3d
    jca
end
