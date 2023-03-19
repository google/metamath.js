include "ch0o.mm"
include "wceq.mm"
include "cado.mm"
include "cfv.mm"
include "fveq2.mm"
include "adj0.mm"
include "syl6eq.mm"
include "cdm.mm"
include "wcel.mm"
include "cbo.mm"
include "bdopssadj.mm"
include "0bdop.mm"
include "sselii.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "dmadjrnb.mm"
include "sylibr.mm"
include "adjadj.mm"
include "syl.mm"
include "a1i.mm"
include "3eqtr3d.mm"
include "impbii.mm"

theorem adjeq0
  let cT: class T


  assert |- ( T = 0hop <-> ( adjh ` T ) = 0hop )

  proof
    cT
    ch0o
    wceq
    #
    cT
    cado
    cfv
    #
    ch0o
    wceq
    #
    @0
    @1
    ch0o
    cado
    cfv
    #
    ch0o
    cT
    ch0o
    cado
    fveq2
    adj0
    syl6eq
    @2
    @1
    cado
    cfv
    #
    @3
    cT
    ch0o
    @1
    ch0o
    cado
    fveq2
    @2
    cT
    cado
    cdm
    #
    wcel
    #
    @4
    cT
    wceq
    @2
    @1
    @5
    wcel
    #
    @6
    @2
    @7
    ch0o
    @5
    wcel
    cbo
    @5
    ch0o
    bdopssadj
    0bdop
    sselii
    @1
    ch0o
    @5
    eleq1
    mpbiri
    cT
    dmadjrnb
    sylibr
    cT
    adjadj
    syl
    @3
    ch0o
    wceq
    @2
    adj0
    a1i
    3eqtr3d
    impbii
end
