include "co.mm"
include "crglmod.mm"
include "cfv.mm"
include "cpws.mm"
include "cplusg.mm"
include "cof.mm"
include "cbs.mm"
include "cress.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "frlmpws.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "cvv.mm"
include "fvex.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"
include "oveqd.mm"
include "fvexd.mm"
include "syl5eq.mm"
include "ressbasss.mm"
include "syl6eqss.mm"
include "sseldd.mm"
include "rlmplusg.mm"
include "eqtri.mm"
include "pwsplusgval.mm"
include "eqtrd.mm"

theorem frlmplusgval
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
  assume frlmplusgval.y: |- Y = ( R freeLMod I )
  assume frlmplusgval.b: |- B = ( Base ` Y )
  assume frlmplusgval.r: |- ( ph -> R e. V )
  assume frlmplusgval.i: |- ( ph -> I e. W )
  assume frlmplusgval.f: |- ( ph -> F e. B )
  assume frlmplusgval.g: |- ( ph -> G e. B )
  assume frlmplusgval.a: |- .+ = ( +g ` R )
  assume frlmplusgval.p: |- .+b = ( +g ` Y )


  assert |- ( ph -> ( F .+b G ) = ( F oF .+ G ) )

  proof
    wph
    cF
    cG
    c.pb
    co
    cF
    cG
    cR
    crglmod
    cfv
    #
    cI
    cpws
    co
    #
    cplusg
    cfv
    #
    co
    cF
    cG
    c.pl
    cof
    co
    wph
    c.pb
    @2
    cF
    cG
    wph
    cY
    cplusg
    cfv
    @1
    cY
    cbs
    cfv
    #
    cress
    co
    #
    cplusg
    cfv
    #
    c.pb
    @2
    wph
    cY
    @4
    cplusg
    wph
    cR
    cV
    wcel
    #
    cI
    cW
    wcel
    #
    cY
    @4
    wceq
    frlmplusgval.r
    frlmplusgval.i
    @3
    cR
    cY
    cI
    cV
    cW
    frlmplusgval.y
    @3
    eqid
    frlmpws
    syl2anc
    fveq2d
    frlmplusgval.p
    @3
    cvv
    wcel
    @2
    @5
    wceq
    cY
    cbs
    fvex
    @3
    @2
    @1
    @4
    cvv
    @4
    eqid
    @2
    eqid
    #
    ressplusg
    ax-mp
    3eqtr4g
    oveqd
    wph
    @1
    cbs
    cfv
    #
    c.pl
    @2
    @0
    cF
    cG
    cI
    cvv
    cW
    @1
    @1
    eqid
    @9
    eqid
    #
    wph
    cR
    crglmod
    fvexd
    frlmplusgval.i
    wph
    cB
    @9
    cF
    wph
    cB
    @1
    cB
    cress
    co
    #
    cbs
    cfv
    #
    @9
    wph
    cB
    @3
    @12
    frlmplusgval.b
    wph
    cY
    @11
    cbs
    wph
    @6
    @7
    cY
    @11
    wceq
    frlmplusgval.r
    frlmplusgval.i
    cB
    cR
    cY
    cI
    cV
    cW
    frlmplusgval.y
    frlmplusgval.b
    frlmpws
    syl2anc
    fveq2d
    syl5eq
    cB
    @9
    @11
    @1
    @11
    eqid
    @10
    ressbasss
    syl6eqss
    #
    frlmplusgval.f
    sseldd
    wph
    cB
    @9
    cG
    @13
    frlmplusgval.g
    sseldd
    c.pl
    cR
    cplusg
    cfv
    @0
    cplusg
    cfv
    frlmplusgval.a
    cR
    rlmplusg
    eqtri
    @8
    pwsplusgval
    eqtrd
end
