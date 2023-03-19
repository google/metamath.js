include "cfn.mm"
include "wcel.mm"
include "crrn.mm"
include "cfv.mm"
include "cms.mm"
include "cn.mm"
include "cv.mm"
include "wf.mm"
include "cmopn.mm"
include "clm.mm"
include "cdm.mm"
include "wi.mm"
include "cca.mm"
include "wral.mm"
include "wa.mm"
include "cmpt.mm"
include "cli.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cr.mm"
include "cxp.mm"
include "cres.mm"
include "eqid.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "rrncmslem.mm"
include "ex.mm"
include "ralrimiva.mm"
include "c1.mm"
include "nnuz.mm"
include "1zzd.mm"
include "rrnmet.mm"
include "iscmet3.mm"
include "mpbird.mm"

theorem rrncms
  let cI: class I
  let cX: class X
  let vf: setvar f
  let vm: setvar m
  let vt: setvar t
  assume rrncms.1: |- X = ( RR ^m I )


  assert |- ( I e. Fin -> ( Rn ` I ) e. ( CMet ` X ) )

  proof
    cI
    cfn
    wcel
    #
    cI
    crrn
    cfv
    #
    cX
    cms
    cfv
    wcel
    cn
    cX
    vf
    cv
    #
    wf
    #
    @2
    @1
    cmopn
    cfv
    #
    clm
    cfv
    cdm
    wcel
    #
    wi
    #
    vf
    @1
    cca
    cfv
    #
    wral
    @0
    @6
    vf
    @7
    @0
    @2
    @7
    wcel
    #
    wa
    #
    @3
    @5
    @9
    @3
    wa
    vt
    vm
    cI
    vt
    cn
    vm
    cv
    vt
    cv
    @2
    cfv
    cfv
    cmpt
    cli
    cfv
    cmpt
    #
    vm
    @2
    cI
    @4
    cabs
    cmin
    ccom
    cr
    cr
    cxp
    cres
    #
    cX
    rrncms.1
    @11
    eqid
    @4
    eqid
    #
    @0
    @8
    @3
    simpll
    @0
    @8
    @3
    simplr
    @9
    @3
    simpr
    @10
    eqid
    rrncmslem
    ex
    ralrimiva
    @0
    @1
    vf
    @4
    c1
    cX
    cn
    nnuz
    @12
    @0
    1zzd
    cI
    cX
    rrncms.1
    rrnmet
    iscmet3
    mpbird
end
