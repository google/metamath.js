include "csca.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "co.mm"
include "cplusg.mm"
include "cv.mm"
include "cmpt.mm"
include "cof.mm"
include "cbs.mm"
include "cvv.mm"
include "eqid.mm"
include "fvexd.mm"
include "wcel.mm"
include "wfn.mm"
include "fnconstg.mm"
include "syl.mm"
include "wceq.mm"
include "pwsval.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "prdsplusgval.mm"
include "wa.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "pwselbas.mm"
include "feqmptd.mm"
include "offval2.mm"
include "3eqtr4d.mm"

theorem pwsplusgval
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let c.x: class .x.
  assume pwsplusgval.y: |- Y = ( R ^s I )
  assume pwsplusgval.b: |- B = ( Base ` Y )
  assume pwsplusgval.r: |- ( ph -> R e. V )
  assume pwsplusgval.i: |- ( ph -> I e. W )
  assume pwsplusgval.f: |- ( ph -> F e. B )
  assume pwsplusgval.g: |- ( ph -> G e. B )
  assume pwsplusgval.a: |- .+ = ( +g ` R )
  assume pwsplusgval.p: |- .+b = ( +g ` Y )


  assert |- ( ph -> ( F .+b G ) = ( F oF .+ G ) )

  proof
    wph
    cF
    cG
    cR
    csca
    cfv
    #
    cI
    cR
    csn
    cxp
    #
    cprds
    co
    #
    cplusg
    cfv
    #
    co
    #
    vx
    cI
    vx
    cv
    #
    cF
    cfv
    #
    @5
    cG
    cfv
    #
    c.pl
    co
    #
    cmpt
    #
    cF
    cG
    c.pb
    co
    cF
    cG
    c.pl
    cof
    co
    wph
    @4
    vx
    cI
    @6
    @7
    @5
    @1
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cmpt
    @9
    wph
    vx
    @2
    cbs
    cfv
    #
    @3
    @1
    @0
    cF
    cG
    cI
    cvv
    cW
    @2
    @2
    eqid
    @13
    eqid
    wph
    cR
    csca
    fvexd
    pwsplusgval.i
    wph
    cR
    cV
    wcel
    #
    @1
    cI
    wfn
    pwsplusgval.r
    cI
    cR
    cV
    fnconstg
    syl
    wph
    cF
    cB
    @13
    pwsplusgval.f
    wph
    cB
    cY
    cbs
    cfv
    @13
    pwsplusgval.b
    wph
    cY
    @2
    cbs
    wph
    @14
    cI
    cW
    wcel
    cY
    @2
    wceq
    pwsplusgval.r
    pwsplusgval.i
    cR
    @0
    cI
    cV
    cW
    cY
    pwsplusgval.y
    @0
    eqid
    pwsval
    syl2anc
    #
    fveq2d
    syl5eq
    #
    eleqtrd
    wph
    cG
    cB
    @13
    pwsplusgval.g
    @16
    eleqtrd
    @3
    eqid
    prdsplusgval
    wph
    vx
    cI
    @12
    @8
    wph
    @5
    cI
    wcel
    #
    wa
    #
    @11
    c.pl
    @6
    @7
    @18
    @11
    cR
    cplusg
    cfv
    c.pl
    @18
    @10
    cR
    cplusg
    wph
    @14
    @17
    @10
    cR
    wceq
    pwsplusgval.r
    cI
    cR
    @5
    cV
    fvconst2g
    sylan
    fveq2d
    pwsplusgval.a
    syl6eqr
    oveqd
    mpteq2dva
    eqtrd
    wph
    c.pb
    @3
    cF
    cG
    wph
    c.pb
    cY
    cplusg
    cfv
    @3
    pwsplusgval.p
    wph
    cY
    @2
    cplusg
    @15
    fveq2d
    syl5eq
    oveqd
    wph
    vx
    cI
    @6
    @7
    c.pl
    cF
    cG
    cW
    cvv
    cvv
    pwsplusgval.i
    @18
    @5
    cF
    fvexd
    @18
    @5
    cG
    fvexd
    wph
    vx
    cI
    cR
    cbs
    cfv
    #
    cF
    wph
    @19
    cR
    cI
    cB
    cV
    cF
    cY
    cW
    pwsplusgval.y
    @19
    eqid
    #
    pwsplusgval.b
    pwsplusgval.r
    pwsplusgval.i
    pwsplusgval.f
    pwselbas
    feqmptd
    wph
    vx
    cI
    @19
    cG
    wph
    @19
    cR
    cI
    cB
    cV
    cG
    cY
    cW
    pwsplusgval.y
    @20
    pwsplusgval.b
    pwsplusgval.r
    pwsplusgval.i
    pwsplusgval.g
    pwselbas
    feqmptd
    offval2
    3eqtr4d
end
