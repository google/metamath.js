include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wf.mm"
include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "eqid.mm"
include "mvrf.mm"
include "ffn.mm"
include "syl.mm"
include "wa.mm"
include "adantr.mm"
include "crg.mm"
include "simpr.mm"
include "mvrcl.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"

theorem mvrf2
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cI: class I
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume mvrf2.p: |- P = ( I mPoly R )
  assume mvrf2.v: |- V = ( I mVar R )
  assume mvrf2.b: |- B = ( Base ` P )
  assume mvrf2.i: |- ( ph -> I e. W )
  assume mvrf2.r: |- ( ph -> R e. Ring )


  assert |- ( ph -> V : I --> B )

  proof
    wph
    cV
    cI
    wfn
    #
    vx
    cv
    #
    cV
    cfv
    cB
    wcel
    #
    vx
    cI
    wral
    cI
    cB
    cV
    wf
    wph
    cI
    cI
    cR
    cmps
    co
    #
    cbs
    cfv
    #
    cV
    wf
    @0
    wph
    @4
    cR
    @3
    cI
    cV
    cW
    @3
    eqid
    mvrf2.v
    @4
    eqid
    mvrf2.i
    mvrf2.r
    mvrf
    cI
    @4
    cV
    ffn
    syl
    wph
    @2
    vx
    cI
    wph
    @1
    cI
    wcel
    #
    wa
    cB
    cP
    cR
    cI
    cV
    cW
    @1
    mvrf2.p
    mvrf2.v
    mvrf2.b
    wph
    cI
    cW
    wcel
    @5
    mvrf2.i
    adantr
    wph
    cR
    crg
    wcel
    @5
    mvrf2.r
    adantr
    wph
    @5
    simpr
    mvrcl
    ralrimiva
    vx
    cI
    cB
    cV
    ffnfv
    sylanbrc
end
