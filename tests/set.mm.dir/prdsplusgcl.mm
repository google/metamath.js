include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cplusg.mm"
include "cmpt.mm"
include "cmnd.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "prdsplusgval.mm"
include "wcel.mm"
include "cbs.mm"
include "wral.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "simpr.mm"
include "prdsbasprj.mm"
include "eqid.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "prdsbasmpt.mm"
include "mpbird.mm"
include "eqeltrd.mm"

theorem prdsplusgcl
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let c.0: class .0.
  assume prdsplusgcl.y: |- Y = ( S Xs_ R )
  assume prdsplusgcl.b: |- B = ( Base ` Y )
  assume prdsplusgcl.p: |- .+ = ( +g ` Y )
  assume prdsplusgcl.s: |- ( ph -> S e. V )
  assume prdsplusgcl.i: |- ( ph -> I e. W )
  assume prdsplusgcl.r: |- ( ph -> R : I --> Mnd )
  assume prdsplusgcl.f: |- ( ph -> F e. B )
  assume prdsplusgcl.g: |- ( ph -> G e. B )


  assert |- ( ph -> ( F .+ G ) e. B )

  proof
    wph
    cF
    cG
    c.pl
    co
    vx
    cI
    vx
    cv
    #
    cF
    cfv
    #
    @0
    cG
    cfv
    #
    @0
    cR
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cmpt
    #
    cB
    wph
    vx
    cB
    c.pl
    cR
    cS
    cF
    cG
    cI
    cV
    cW
    cY
    prdsplusgcl.y
    prdsplusgcl.b
    prdsplusgcl.s
    prdsplusgcl.i
    wph
    cI
    cmnd
    cR
    wf
    cR
    cI
    wfn
    #
    prdsplusgcl.r
    cI
    cmnd
    cR
    ffn
    syl
    #
    prdsplusgcl.f
    prdsplusgcl.g
    prdsplusgcl.p
    prdsplusgval
    wph
    @6
    cB
    wcel
    @5
    @3
    cbs
    cfv
    #
    wcel
    #
    vx
    cI
    wral
    wph
    @10
    vx
    cI
    wph
    @0
    cI
    wcel
    #
    wa
    #
    @3
    cmnd
    wcel
    @1
    @9
    wcel
    @2
    @9
    wcel
    @10
    wph
    cI
    cmnd
    @0
    cR
    prdsplusgcl.r
    ffvelrnda
    @12
    cB
    cR
    cS
    cF
    cI
    @0
    cV
    cW
    cY
    prdsplusgcl.y
    prdsplusgcl.b
    wph
    cS
    cV
    wcel
    @11
    prdsplusgcl.s
    adantr
    #
    wph
    cI
    cW
    wcel
    @11
    prdsplusgcl.i
    adantr
    #
    wph
    @7
    @11
    @8
    adantr
    #
    wph
    cF
    cB
    wcel
    @11
    prdsplusgcl.f
    adantr
    wph
    @11
    simpr
    #
    prdsbasprj
    @12
    cB
    cR
    cS
    cG
    cI
    @0
    cV
    cW
    cY
    prdsplusgcl.y
    prdsplusgcl.b
    @13
    @14
    @15
    wph
    cG
    cB
    wcel
    @11
    prdsplusgcl.g
    adantr
    @16
    prdsbasprj
    @9
    @4
    @3
    @1
    @2
    @9
    eqid
    @4
    eqid
    mndcl
    syl3anc
    ralrimiva
    wph
    vx
    cB
    cR
    cS
    @5
    cI
    cV
    cW
    cY
    prdsplusgcl.y
    prdsplusgcl.b
    prdsplusgcl.s
    prdsplusgcl.i
    @8
    prdsbasmpt
    mpbird
    eqeltrd
end
