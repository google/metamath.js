include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmulr.mm"
include "cmpt.mm"
include "crg.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "prdsmulrval.mm"
include "wcel.mm"
include "cbs.mm"
include "wral.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "simpr.mm"
include "prdsbasprj.mm"
include "eqid.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "prdsbasmpt.mm"
include "mpbird.mm"
include "eqeltrd.mm"

theorem prdsmulrcl
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let vx: setvar x
  assume prdsmulrcl.y: |- Y = ( S Xs_ R )
  assume prdsmulrcl.b: |- B = ( Base ` Y )
  assume prdsmulrcl.t: |- .x. = ( .r ` Y )
  assume prdsmulrcl.s: |- ( ph -> S e. V )
  assume prdsmulrcl.i: |- ( ph -> I e. W )
  assume prdsmulrcl.r: |- ( ph -> R : I --> Ring )
  assume prdsmulrcl.f: |- ( ph -> F e. B )
  assume prdsmulrcl.g: |- ( ph -> G e. B )


  assert |- ( ph -> ( F .x. G ) e. B )

  proof
    wph
    cF
    cG
    c.x
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
    cmulr
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
    cR
    cS
    c.x
    cF
    cG
    cI
    cV
    cW
    cY
    prdsmulrcl.y
    prdsmulrcl.b
    prdsmulrcl.s
    prdsmulrcl.i
    wph
    cI
    crg
    cR
    wf
    cR
    cI
    wfn
    #
    prdsmulrcl.r
    cI
    crg
    cR
    ffn
    syl
    #
    prdsmulrcl.f
    prdsmulrcl.g
    prdsmulrcl.t
    prdsmulrval
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
    crg
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
    crg
    @0
    cR
    prdsmulrcl.r
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
    prdsmulrcl.y
    prdsmulrcl.b
    wph
    cS
    cV
    wcel
    @11
    prdsmulrcl.s
    adantr
    #
    wph
    cI
    cW
    wcel
    @11
    prdsmulrcl.i
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
    prdsmulrcl.f
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
    prdsmulrcl.y
    prdsmulrcl.b
    @13
    @14
    @15
    wph
    cG
    cB
    wcel
    @11
    prdsmulrcl.g
    adantr
    @16
    prdsbasprj
    @9
    @3
    @4
    @1
    @2
    @9
    eqid
    @4
    eqid
    ringcl
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
    prdsmulrcl.y
    prdsmulrcl.b
    prdsmulrcl.s
    prdsmulrcl.i
    @8
    prdsbasmpt
    mpbird
    eqeltrd
end
