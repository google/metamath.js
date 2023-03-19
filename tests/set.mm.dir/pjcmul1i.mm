include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "crn.mm"
include "wcel.mm"
include "cin.mm"
include "pjclem4.mm"
include "cch.mm"
include "wfn.mm"
include "pjmfn.mm"
include "chincli.mm"
include "fnfvelrn.mm"
include "mp2an.mm"
include "syl6eqel.mm"
include "cado.mm"
include "pjbdlni.mm"
include "adjcoi.mm"
include "pjadj3.mm"
include "ax-mp.mm"
include "coeq12i.mm"
include "eqtri.mm"
include "pjadj2.mm"
include "syl5reqr.mm"
include "impbii.mm"

theorem pjcmul1i
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjclem1.1: |- G e. CH
  assume pjclem1.2: |- H e. CH


  assert |- ( ( ( projh ` G ) o. ( projh ` H ) ) = ( ( projh ` H ) o. ( projh ` G ) ) <-> ( ( projh ` G ) o. ( projh ` H ) ) e. ran projh )

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
    #
    wceq
    #
    @2
    cpjh
    crn
    #
    wcel
    #
    @4
    @2
    cG
    cH
    cin
    #
    cpjh
    cfv
    #
    @5
    cG
    cH
    pjclem1.1
    pjclem1.2
    pjclem4
    cpjh
    cch
    wfn
    @7
    cch
    wcel
    @8
    @5
    wcel
    pjmfn
    cG
    cH
    pjclem1.1
    pjclem1.2
    chincli
    cch
    @7
    cpjh
    fnfvelrn
    mp2an
    syl6eqel
    @6
    @3
    @2
    cado
    cfv
    #
    @2
    @9
    @1
    cado
    cfv
    #
    @0
    cado
    cfv
    #
    ccom
    @3
    @0
    @1
    cG
    pjclem1.1
    pjbdlni
    cH
    pjclem1.2
    pjbdlni
    adjcoi
    @10
    @1
    @11
    @0
    cH
    cch
    wcel
    @10
    @1
    wceq
    pjclem1.2
    cH
    pjadj3
    ax-mp
    cG
    cch
    wcel
    @11
    @0
    wceq
    pjclem1.1
    cG
    pjadj3
    ax-mp
    coeq12i
    eqtri
    @2
    pjadj2
    syl5reqr
    impbii
end
