include "wcel.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "crio.mm"
include "chlt.mm"
include "hgmapval.mm"
include "eqcomd.mm"
include "wreu.mm"
include "wb.mm"
include "hgmapcl.mm"
include "hdmap14lem15.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "rspcva.mm"

theorem hgmapvs
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let vg: setvar g
  let vx: setvar x
  assume hgmapvs.h: |- H = ( LHyp ` K )
  assume hgmapvs.u: |- U = ( ( DVecH ` K ) ` W )
  assume hgmapvs.v: |- V = ( Base ` U )
  assume hgmapvs.t: |- .x. = ( .s ` U )
  assume hgmapvs.r: |- R = ( Scalar ` U )
  assume hgmapvs.b: |- B = ( Base ` R )
  assume hgmapvs.c: |- C = ( ( LCDual ` K ) ` W )
  assume hgmapvs.e: |- .xb = ( .s ` C )
  assume hgmapvs.s: |- S = ( ( HDMap ` K ) ` W )
  assume hgmapvs.g: |- G = ( ( HGMap ` K ) ` W )
  assume hgmapvs.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hgmapvs.x: |- ( ph -> X e. V )
  assume hgmapvs.f: |- ( ph -> F e. B )


  assert |- ( ph -> ( S ` ( F .x. X ) ) = ( ( G ` F ) .xb ( S ` X ) ) )

  proof
    wph
    cX
    cV
    wcel
    cF
    vx
    cv
    #
    c.x
    co
    #
    cS
    cfv
    #
    cF
    cG
    cfv
    #
    @0
    cS
    cfv
    #
    c.xb
    co
    #
    wceq
    #
    vx
    cV
    wral
    #
    cF
    cX
    c.x
    co
    #
    cS
    cfv
    #
    @3
    cX
    cS
    cfv
    #
    c.xb
    co
    #
    wceq
    #
    hgmapvs.x
    wph
    @7
    @2
    vg
    cv
    #
    @4
    c.xb
    co
    #
    wceq
    #
    vx
    cV
    wral
    #
    vg
    cB
    crio
    #
    @3
    wceq
    #
    wph
    @3
    @17
    wph
    vg
    vx
    cB
    cC
    cR
    c.xb
    c.x
    cU
    cH
    cG
    cK
    cS
    cV
    cW
    cF
    chlt
    hgmapvs.h
    hgmapvs.u
    hgmapvs.v
    hgmapvs.t
    hgmapvs.r
    hgmapvs.b
    hgmapvs.c
    hgmapvs.e
    hgmapvs.s
    hgmapvs.g
    hgmapvs.k
    hgmapvs.f
    hgmapval
    eqcomd
    wph
    @3
    cB
    wcel
    @16
    vg
    cB
    wreu
    @7
    @18
    wb
    wph
    cB
    cR
    cU
    cF
    cG
    cH
    cK
    cW
    hgmapvs.h
    hgmapvs.u
    hgmapvs.r
    hgmapvs.b
    hgmapvs.g
    hgmapvs.k
    hgmapvs.f
    hgmapcl
    wph
    vx
    cB
    cC
    cR
    cS
    c.xb
    c.x
    cU
    vg
    cF
    cH
    cK
    cV
    cW
    hgmapvs.h
    hgmapvs.u
    hgmapvs.v
    hgmapvs.t
    hgmapvs.r
    hgmapvs.b
    hgmapvs.c
    hgmapvs.e
    hgmapvs.s
    hgmapvs.k
    hgmapvs.f
    hdmap14lem15
    @16
    @7
    vg
    cB
    @3
    @13
    @3
    wceq
    #
    @15
    @6
    vx
    cV
    @19
    @14
    @5
    @2
    @13
    @3
    @4
    c.xb
    oveq1
    eqeq2d
    ralbidv
    riota2
    syl2anc
    mpbird
    @6
    @12
    vx
    cX
    cV
    @0
    cX
    wceq
    #
    @2
    @9
    @5
    @11
    @20
    @1
    @8
    cS
    @0
    cX
    cF
    c.x
    oveq2
    fveq2d
    @20
    @4
    @10
    @3
    c.xb
    @0
    cX
    cS
    fveq2
    oveq2d
    eqeq12d
    rspcva
    syl2anc
end
