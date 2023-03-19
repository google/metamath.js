include "cms.mm"
include "cfv.mm"
include "wcel.mm"
include "cme.mm"
include "cca.mm"
include "clm.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "cmetmet.mm"
include "cv.mm"
include "cmetcau.mm"
include "ex.mm"
include "ssrdv.mm"
include "jca.mm"
include "cn.mm"
include "wf.mm"
include "wi.mm"
include "wral.mm"
include "ssel2.mm"
include "a1d.mm"
include "ralrimiva.mm"
include "adantl.mm"
include "c1.mm"
include "nnuz.mm"
include "1zzd.mm"
include "simpl.mm"
include "iscmet3.mm"
include "mpbird.mm"
include "impbii.mm"

theorem iscmet2
  let cD: class D
  let cJ: class J
  let cX: class X
  let vf: setvar f
  assume iscmet2.1: |- J = ( MetOpen ` D )


  assert |- ( D e. ( CMet ` X ) <-> ( D e. ( Met ` X ) /\ ( Cau ` D ) C_ dom ( ~~>t ` J ) ) )

  proof
    cD
    cX
    cms
    cfv
    wcel
    #
    cD
    cX
    cme
    cfv
    wcel
    #
    cD
    cca
    cfv
    #
    cJ
    clm
    cfv
    cdm
    #
    wss
    #
    wa
    #
    @0
    @1
    @4
    cD
    cX
    cmetmet
    @0
    vf
    @2
    @3
    @0
    vf
    cv
    #
    @2
    wcel
    #
    @6
    @3
    wcel
    #
    cD
    @6
    cJ
    cX
    iscmet2.1
    cmetcau
    ex
    ssrdv
    jca
    @5
    @0
    cn
    cX
    @6
    wf
    #
    @8
    wi
    #
    vf
    @2
    wral
    #
    @4
    @11
    @1
    @4
    @10
    vf
    @2
    @4
    @7
    wa
    @8
    @9
    @2
    @3
    @6
    ssel2
    a1d
    ralrimiva
    adantl
    @5
    cD
    vf
    cJ
    c1
    cX
    cn
    nnuz
    iscmet2.1
    @5
    1zzd
    @1
    @4
    simpl
    iscmet3
    mpbird
    impbii
end
