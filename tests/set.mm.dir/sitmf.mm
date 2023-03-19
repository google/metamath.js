include "csitg.mm"
include "co.mm"
include "cdm.mm"
include "cxp.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "csitm.mm"
include "wf.mm"
include "cv.mm"
include "cds.mm"
include "cfv.mm"
include "cof.mm"
include "cxrs.mm"
include "cress.mm"
include "cmpt2.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cxme.mm"
include "eqid.mm"
include "adantr.mm"
include "cmeas.mm"
include "crn.mm"
include "cuni.mm"
include "simprl.mm"
include "simprr.mm"
include "sitmfval.mm"
include "cmnd.mm"
include "sitmcl.mm"
include "eqeltrrd.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "sylib.mm"
include "sitmval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem sitmf
  let wph: wff ph
  let cM: class M
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  assume sitmf.0: |- ( ph -> W e. Mnd )
  assume sitmf.1: |- ( ph -> W e. *MetSp )
  assume sitmf.2: |- ( ph -> M e. U. ran measures )


  assert |- ( ph -> ( W sitm M ) : ( dom ( W sitg M ) X. dom ( W sitg M ) ) --> ( 0 [,] +oo ) )

  proof
    wph
    cW
    cM
    csitg
    co
    cdm
    #
    @0
    cxp
    #
    cc0
    cpnf
    cicc
    co
    #
    cW
    cM
    csitm
    co
    #
    wf
    @1
    @2
    vf
    vg
    @0
    @0
    vf
    cv
    #
    vg
    cv
    #
    cW
    cds
    cfv
    #
    cof
    co
    cxrs
    @2
    cress
    co
    cM
    csitg
    co
    cfv
    #
    cmpt2
    #
    wf
    #
    wph
    @7
    @2
    wcel
    #
    vg
    @0
    wral
    vf
    @0
    wral
    @9
    wph
    @10
    vf
    vg
    @0
    @0
    wph
    @4
    @0
    wcel
    #
    @5
    @0
    wcel
    #
    wa
    #
    wa
    #
    @4
    @5
    @3
    co
    @7
    @2
    @14
    @6
    @4
    @5
    cM
    cxme
    cW
    @6
    eqid
    #
    wph
    cW
    cxme
    wcel
    @13
    sitmf.1
    adantr
    #
    wph
    cM
    cmeas
    crn
    cuni
    wcel
    @13
    sitmf.2
    adantr
    #
    wph
    @11
    @12
    simprl
    #
    wph
    @11
    @12
    simprr
    #
    sitmfval
    @14
    @4
    @5
    cM
    cW
    wph
    cW
    cmnd
    wcel
    @13
    sitmf.0
    adantr
    @16
    @17
    @18
    @19
    sitmcl
    eqeltrrd
    ralrimivva
    vf
    vg
    @0
    @0
    @7
    @2
    @8
    @8
    eqid
    fmpt2
    sylib
    wph
    @1
    @2
    @3
    @8
    wph
    @6
    vf
    vg
    cM
    cxme
    cW
    @15
    sitmf.1
    sitmf.2
    sitmval
    feq1d
    mpbird
end
