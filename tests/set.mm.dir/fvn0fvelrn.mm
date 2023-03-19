include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "cdm.mm"
include "wcel.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wa.mm"
include "crn.mm"
include "fvfundmfvn0.mm"
include "wi.mm"
include "eldmressnsn.mm"
include "fvelrn.mm"
include "pm3.2.mm"
include "syl.mm"
include "ex.mm"
include "com13.mm"
include "mpd.mm"
include "imp.mm"
include "fvressn.mm"
include "eleq1d.mm"
include "fvrnressn.mm"
include "sylbid.mm"
include "impcom.mm"
include "3syl.mm"

theorem fvn0fvelrn
  let cF: class F
  let cX: class X


  assert |- ( ( F ` X ) =/= (/) -> ( F ` X ) e. ran F )

  proof
    cX
    cF
    cfv
    #
    c0
    wne
    cX
    cF
    cdm
    #
    wcel
    #
    cF
    cX
    csn
    cres
    #
    wfun
    #
    wa
    cX
    @3
    cfv
    #
    @3
    crn
    #
    wcel
    #
    @2
    wa
    #
    @0
    cF
    crn
    wcel
    #
    cX
    cF
    fvfundmfvn0
    @2
    @4
    @8
    @2
    cX
    @3
    cdm
    wcel
    #
    @4
    @8
    wi
    cX
    cF
    eldmressnsn
    @4
    @10
    @2
    @8
    @4
    @10
    @2
    @8
    wi
    #
    @4
    @10
    wa
    @7
    @11
    cX
    @3
    fvelrn
    @7
    @2
    pm3.2
    syl
    ex
    com13
    mpd
    imp
    @2
    @7
    @9
    @2
    @7
    @0
    @6
    wcel
    @9
    @2
    @5
    @0
    @6
    cF
    @1
    cX
    fvressn
    eleq1d
    cF
    @1
    cX
    fvrnressn
    sylbid
    impcom
    3syl
end
