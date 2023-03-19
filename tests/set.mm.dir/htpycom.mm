include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "cmpt2.mm"
include "cii.mm"
include "ctx.mm"
include "ccn.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "iitopon.mm"
include "a1i.mm"
include "cnmpt1st.mm"
include "cnmpt2nd.mm"
include "cmpt.mm"
include "iirevcn.mm"
include "oveq2.mm"
include "cnmpt21.mm"
include "chtpy.mm"
include "htpycn.mm"
include "sseldd.mm"
include "cnmpt22f.mm"
include "syl5eqel.mm"
include "wa.mm"
include "wceq.mm"
include "simpr.mm"
include "0elunit.mm"
include "oveq1.mm"
include "1m0e1.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "ovex.mm"
include "ovmpt2.mm"
include "sylancl.mm"
include "htpyi.mm"
include "simprd.mm"
include "eqtrd.mm"
include "1elunit.mm"
include "1m1e0.mm"
include "simpld.mm"
include "ishtpyd.mm"

theorem htpycom
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let cX: class X
  let cA: class A
  let vs: setvar s
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vj: setvar j
  let vk: setvar k
  let vz: setvar z
  assume ishtpy.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume ishtpy.3: |- ( ph -> F e. ( J Cn K ) )
  assume ishtpy.4: |- ( ph -> G e. ( J Cn K ) )
  assume htpycom.6: |- M = ( x e. X , y e. ( 0 [,] 1 ) |-> ( x H ( 1 - y ) ) )
  assume htpycom.7: |- ( ph -> H e. ( F ( J Htpy K ) G ) )

  disjoint x y
  disjoint H x
  disjoint H y
  disjoint J x
  disjoint J y
  disjoint ph x
  disjoint ph y
  disjoint K x
  disjoint K y
  disjoint X x
  disjoint X y
  disjoint A s
  disjoint f g
  disjoint f h
  disjoint f s
  disjoint f t
  disjoint F f
  disjoint g h
  disjoint g s
  disjoint g t
  disjoint F g
  disjoint h s
  disjoint h t
  disjoint F h
  disjoint s t
  disjoint F s
  disjoint F t
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G s
  disjoint G t
  disjoint h x
  disjoint h y
  disjoint H h
  disjoint s x
  disjoint s y
  disjoint H s
  disjoint M t
  disjoint f j
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint J f
  disjoint g j
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint J g
  disjoint h j
  disjoint h k
  disjoint h z
  disjoint J h
  disjoint j k
  disjoint j s
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint k s
  disjoint k t
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint J k
  disjoint s z
  disjoint J s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint J t
  disjoint x z
  disjoint y z
  disjoint J z
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint j ph
  disjoint k ph
  disjoint ph s
  disjoint ph t
  disjoint ph z
  disjoint K f
  disjoint K g
  disjoint K h
  disjoint K j
  disjoint K k
  disjoint X f
  disjoint X g
  disjoint X h
  disjoint X j
  disjoint X k
  disjoint X s
  disjoint X t
  disjoint X z
  assert |- ( ph -> M e. ( G ( J Htpy K ) F ) )

  proof
    wph
    cG
    cF
    cM
    cJ
    cK
    cX
    vt
    ishtpy.1
    ishtpy.4
    ishtpy.3
    wph
    cM
    vx
    vy
    cX
    cc0
    c1
    cicc
    co
    #
    vx
    cv
    #
    c1
    vy
    cv
    #
    cmin
    co
    #
    cH
    co
    #
    cmpt2
    cJ
    cii
    ctx
    co
    cK
    ccn
    co
    #
    htpycom.6
    wph
    vx
    vy
    @1
    @3
    cH
    cJ
    cii
    cJ
    cii
    cK
    cX
    @0
    ishtpy.1
    cii
    @0
    ctopon
    cfv
    wcel
    wph
    iitopon
    a1i
    #
    wph
    vx
    vy
    cJ
    cii
    cX
    @0
    ishtpy.1
    @6
    cnmpt1st
    wph
    vx
    vy
    vz
    @2
    c1
    vz
    cv
    #
    cmin
    co
    #
    @3
    cJ
    cii
    cii
    cii
    cX
    @0
    @0
    ishtpy.1
    @6
    wph
    vx
    vy
    cJ
    cii
    cX
    @0
    ishtpy.1
    @6
    cnmpt2nd
    @6
    vz
    @0
    @8
    cmpt
    cii
    cii
    ccn
    co
    wcel
    wph
    vz
    iirevcn
    a1i
    @7
    @2
    c1
    cmin
    oveq2
    cnmpt21
    wph
    cF
    cG
    cJ
    cK
    chtpy
    co
    co
    @5
    cH
    wph
    cF
    cG
    cJ
    cK
    cX
    ishtpy.1
    ishtpy.3
    ishtpy.4
    htpycn
    htpycom.7
    sseldd
    cnmpt22f
    syl5eqel
    wph
    vt
    cv
    #
    cX
    wcel
    #
    wa
    #
    @9
    cc0
    cM
    co
    #
    @9
    c1
    cH
    co
    #
    @9
    cG
    cfv
    #
    @11
    @10
    cc0
    @0
    wcel
    @12
    @13
    wceq
    wph
    @10
    simpr
    #
    0elunit
    vx
    vy
    @9
    cc0
    cX
    @0
    @4
    @13
    cM
    @9
    @3
    cH
    co
    #
    @1
    @9
    @3
    cH
    oveq1
    #
    @2
    cc0
    wceq
    #
    @3
    c1
    @9
    cH
    @18
    @3
    c1
    cc0
    cmin
    co
    c1
    @2
    cc0
    c1
    cmin
    oveq2
    1m0e1
    syl6eq
    oveq2d
    htpycom.6
    @9
    c1
    cH
    ovex
    ovmpt2
    sylancl
    @11
    @9
    cc0
    cH
    co
    #
    @9
    cF
    cfv
    #
    wceq
    #
    @13
    @14
    wceq
    #
    wph
    @9
    cF
    cG
    cH
    cJ
    cK
    cX
    ishtpy.1
    ishtpy.3
    ishtpy.4
    htpycom.7
    htpyi
    #
    simprd
    eqtrd
    @11
    @9
    c1
    cM
    co
    #
    @19
    @20
    @11
    @10
    c1
    @0
    wcel
    @24
    @19
    wceq
    @15
    1elunit
    vx
    vy
    @9
    c1
    cX
    @0
    @4
    @19
    cM
    @16
    @17
    @2
    c1
    wceq
    #
    @3
    cc0
    @9
    cH
    @25
    @3
    c1
    c1
    cmin
    co
    cc0
    @2
    c1
    c1
    cmin
    oveq2
    1m1e0
    syl6eq
    oveq2d
    htpycom.6
    @9
    cc0
    cH
    ovex
    ovmpt2
    sylancl
    @11
    @21
    @22
    @23
    simpld
    eqtrd
    ishtpyd
end
