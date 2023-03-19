include "cop.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "ismon2.mm"
include "mpbid.mm"
include "simprd.mm"
include "adantr.mm"
include "simpr.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"
include "simpllr.mm"
include "opeq1d.mm"
include "eqidd.mm"
include "simplr.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspcdv.mm"
include "rspcimdv.mm"
include "mpd.mm"
include "oveq2.mm"
include "impbid1.mm"

theorem moni
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ismon.b: |- B = ( Base ` C )
  assume ismon.h: |- H = ( Hom ` C )
  assume ismon.o: |- .x. = ( comp ` C )
  assume ismon.s: |- M = ( Mono ` C )
  assume ismon.c: |- ( ph -> C e. Cat )
  assume ismon.x: |- ( ph -> X e. B )
  assume ismon.y: |- ( ph -> Y e. B )
  assume moni.z: |- ( ph -> Z e. B )
  assume moni.f: |- ( ph -> F e. ( X M Y ) )
  assume moni.g: |- ( ph -> G e. ( Z H X ) )
  assume moni.k: |- ( ph -> K e. ( Z H X ) )


  assert |- ( ph -> ( ( F ( <. Z , X >. .x. Y ) G ) = ( F ( <. Z , X >. .x. Y ) K ) <-> G = K ) )

  proof
    wph
    cF
    cG
    cZ
    cX
    cop
    #
    cY
    c.x
    co
    #
    co
    #
    cF
    cK
    @1
    co
    #
    wceq
    #
    cG
    cK
    wceq
    #
    wph
    cF
    vg
    cv
    #
    vz
    cv
    #
    cX
    cop
    #
    cY
    c.x
    co
    #
    co
    #
    cF
    vh
    cv
    #
    @9
    co
    #
    wceq
    #
    @6
    @11
    wceq
    #
    wi
    #
    vh
    @7
    cX
    cH
    co
    #
    wral
    #
    vg
    @16
    wral
    #
    vz
    cB
    wral
    #
    @4
    @5
    wi
    #
    wph
    cF
    cX
    cY
    cH
    co
    wcel
    #
    @19
    wph
    cF
    cX
    cY
    cM
    co
    wcel
    @21
    @19
    wa
    moni.f
    wph
    vz
    cB
    cC
    c.x
    vg
    vh
    cF
    cH
    cM
    cX
    cY
    ismon.b
    ismon.h
    ismon.o
    ismon.s
    ismon.c
    ismon.x
    ismon.y
    ismon2
    mpbid
    simprd
    wph
    @18
    @20
    vz
    cZ
    cB
    moni.z
    wph
    @7
    cZ
    wceq
    #
    wa
    #
    @17
    @20
    vg
    cG
    @16
    @23
    cG
    cZ
    cX
    cH
    co
    #
    @16
    wph
    cG
    @24
    wcel
    @22
    moni.g
    adantr
    @23
    @7
    cZ
    cX
    cH
    wph
    @22
    simpr
    oveq1d
    #
    eleqtrrd
    @23
    @6
    cG
    wceq
    #
    wa
    #
    @15
    @20
    vh
    cK
    @16
    @23
    cK
    @16
    wcel
    @26
    @23
    cK
    @24
    @16
    wph
    cK
    @24
    wcel
    @22
    moni.k
    adantr
    @25
    eleqtrrd
    adantr
    @27
    @11
    cK
    wceq
    #
    wa
    #
    @13
    @4
    @14
    @5
    @29
    @10
    @2
    @12
    @3
    @29
    cF
    cF
    @6
    cG
    @9
    @1
    @29
    @8
    @0
    cY
    c.x
    @29
    @7
    cZ
    cX
    wph
    @22
    @26
    @28
    simpllr
    opeq1d
    oveq1d
    #
    @29
    cF
    eqidd
    #
    @23
    @26
    @28
    simplr
    #
    oveq123d
    @29
    cF
    cF
    @11
    cK
    @9
    @1
    @30
    @31
    @27
    @28
    simpr
    #
    oveq123d
    eqeq12d
    @29
    @6
    cG
    @11
    cK
    @32
    @33
    eqeq12d
    imbi12d
    rspcdv
    rspcimdv
    rspcimdv
    mpd
    cG
    cK
    cF
    @1
    oveq2
    impbid1
end
