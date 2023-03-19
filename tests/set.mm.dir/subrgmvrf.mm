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
include "csubrg.mm"
include "crg.mm"
include "subrgrcl.mm"
include "syl.mm"
include "mvrf.mm"
include "ffn.mm"
include "wa.mm"
include "cmvr.mm"
include "wceq.mm"
include "subrgmvr.mm"
include "fveq1d.mm"
include "adantr.mm"
include "subrgring.mm"
include "simpr.mm"
include "mvrcl.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"

theorem subrgmvrf
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cT: class T
  let cU: class U
  let cH: class H
  let cI: class I
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vz: setvar z
  assume subrgmvr.v: |- V = ( I mVar R )
  assume subrgmvr.i: |- ( ph -> I e. W )
  assume subrgmvr.r: |- ( ph -> T e. ( SubRing ` R ) )
  assume subrgmvr.h: |- H = ( R |`s T )
  assume subrgmvrf.u: |- U = ( I mPoly H )
  assume subrgmvrf.b: |- B = ( Base ` U )


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
    #
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
    @5
    cR
    @4
    cI
    cV
    cW
    @4
    eqid
    subrgmvr.v
    @5
    eqid
    subrgmvr.i
    wph
    cT
    cR
    csubrg
    cfv
    wcel
    #
    cR
    crg
    wcel
    subrgmvr.r
    cT
    cR
    subrgrcl
    syl
    mvrf
    cI
    @5
    cV
    ffn
    syl
    wph
    @3
    vx
    cI
    wph
    @1
    cI
    wcel
    #
    wa
    #
    @2
    @1
    cI
    cH
    cmvr
    co
    #
    cfv
    #
    cB
    wph
    @2
    @10
    wceq
    @7
    wph
    @1
    cV
    @9
    wph
    cR
    cT
    cH
    cI
    cV
    cW
    subrgmvr.v
    subrgmvr.i
    subrgmvr.r
    subrgmvr.h
    subrgmvr
    fveq1d
    adantr
    @8
    cB
    cU
    cH
    cI
    @9
    cW
    @1
    subrgmvrf.u
    @9
    eqid
    subrgmvrf.b
    wph
    cI
    cW
    wcel
    @7
    subrgmvr.i
    adantr
    wph
    cH
    crg
    wcel
    #
    @7
    wph
    @6
    @11
    subrgmvr.r
    cT
    cR
    cH
    subrgmvr.h
    subrgring
    syl
    adantr
    wph
    @7
    simpr
    mvrcl
    eqeltrd
    ralrimiva
    vx
    cI
    cB
    cV
    ffnfv
    sylanbrc
end
