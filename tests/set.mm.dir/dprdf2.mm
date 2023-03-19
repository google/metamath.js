include "cdm.mm"
include "csubg.mm"
include "cfv.mm"
include "wf.mm"
include "cdprd.mm"
include "wbr.mm"
include "dprdf.mm"
include "syl.mm"
include "feq2d.mm"
include "mpbid.mm"

theorem dprdf2
  let wph: wff ph
  let cS: class S
  let cG: class G
  let cI: class I
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume dprdcntz.1: |- ( ph -> G dom DProd S )
  assume dprdcntz.2: |- ( ph -> dom S = I )


  assert |- ( ph -> S : I --> ( SubGrp ` G ) )

  proof
    wph
    cS
    cdm
    #
    cG
    csubg
    cfv
    #
    cS
    wf
    #
    cI
    @1
    cS
    wf
    wph
    cG
    cS
    cdprd
    cdm
    wbr
    @2
    dprdcntz.1
    cS
    cG
    dprdf
    syl
    wph
    @0
    cI
    @1
    cS
    dprdcntz.2
    feq2d
    mpbid
end
