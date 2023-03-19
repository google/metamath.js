include "c0.mm"
include "wceq.mm"
include "ctotbnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cme.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "cv.mm"
include "cbl.mm"
include "co.mm"
include "ciun.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "0elpw.mm"
include "0fin.mm"
include "elin.mm"
include "mpbir2an.mm"
include "0iun.mm"
include "iuneq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "rgenw.mm"
include "istotbnd3.mm"
include "mpbiran2.mm"
include "syl6rbbr.mm"
include "bitrd.mm"

theorem 0totbnd
  let cM: class M
  let cX: class X
  let vr: setvar r
  let vv: setvar v
  let vx: setvar x


  assert |- ( X = (/) -> ( M e. ( TotBnd ` X ) <-> M e. ( Met ` X ) ) )

  proof
    cX
    c0
    wceq
    #
    cM
    cX
    ctotbnd
    cfv
    #
    wcel
    cM
    c0
    ctotbnd
    cfv
    #
    wcel
    #
    cM
    cX
    cme
    cfv
    #
    wcel
    #
    @0
    @1
    @2
    cM
    cX
    c0
    ctotbnd
    fveq2
    eleq2d
    @0
    @5
    cM
    c0
    cme
    cfv
    #
    wcel
    #
    @3
    @0
    @4
    @6
    cM
    cX
    c0
    cme
    fveq2
    eleq2d
    @3
    @7
    vx
    vv
    cv
    #
    vx
    cv
    vr
    cv
    cM
    cbl
    cfv
    co
    #
    ciun
    #
    c0
    wceq
    #
    vv
    c0
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    vr
    crp
    wral
    @14
    vr
    crp
    c0
    @13
    wcel
    #
    vx
    c0
    @9
    ciun
    #
    c0
    wceq
    #
    @14
    @15
    c0
    @12
    wcel
    c0
    cfn
    wcel
    c0
    0elpw
    0fin
    c0
    @12
    cfn
    elin
    mpbir2an
    vx
    @9
    0iun
    @11
    @17
    vv
    c0
    @13
    @8
    c0
    wceq
    @10
    @16
    c0
    vx
    @8
    c0
    @9
    iuneq1
    eqeq1d
    rspcev
    mp2an
    rgenw
    vx
    vv
    cM
    c0
    vr
    istotbnd3
    mpbiran2
    syl6rbbr
    bitrd
end
