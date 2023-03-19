include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "cin.mm"
include "pjclem4.mm"
include "crn.mm"
include "wcel.mm"
include "cch.mm"
include "wfn.mm"
include "pjmfn.mm"
include "chincli.mm"
include "fnfvelrn.mm"
include "mp2an.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "pjcmul1i.mm"
include "sylibr.mm"
include "impbii.mm"

theorem pjcmul2i
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjclem1.1: |- G e. CH
  assume pjclem1.2: |- H e. CH


  assert |- ( ( ( projh ` G ) o. ( projh ` H ) ) = ( ( projh ` H ) o. ( projh ` G ) ) <-> ( ( projh ` G ) o. ( projh ` H ) ) = ( projh ` ( G i^i H ) ) )

  proof
    cG
    cpjh
    cfv
    #
    cH
    cpjh
    cfv
    #
    ccom
    #
    @1
    @0
    ccom
    wceq
    #
    @2
    cG
    cH
    cin
    #
    cpjh
    cfv
    #
    wceq
    #
    cG
    cH
    pjclem1.1
    pjclem1.2
    pjclem4
    @6
    @2
    cpjh
    crn
    #
    wcel
    #
    @3
    @6
    @8
    @5
    @7
    wcel
    #
    cpjh
    cch
    wfn
    @4
    cch
    wcel
    @9
    pjmfn
    cG
    cH
    pjclem1.1
    pjclem1.2
    chincli
    cch
    @4
    cpjh
    fnfvelrn
    mp2an
    @2
    @5
    @7
    eleq1
    mpbiri
    cG
    cH
    pjclem1.1
    pjclem1.2
    pjcmul1i
    sylibr
    impbii
end
