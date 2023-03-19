include "crg.mm"
include "wcel.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "ccrg.mm"
include "c0.mm"
include "cfn.mm"
include "0fin.mm"
include "matring.mm"
include "mpan.mm"
include "cmat.mm"
include "csn.mm"
include "mat0dimbas0.mm"
include "wi.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "eqeq1i.mm"
include "wa.mm"
include "eqidd.mm"
include "0ex.mm"
include "oveq1.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "ralsn.mm"
include "bitri.mm"
include "sylibr.mm"
include "wb.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "adantr.mm"
include "mpbird.mm"
include "ex.mm"
include "sylbi.mm"
include "mpcom.mm"
include "eqid.mm"
include "iscrng2.mm"
include "sylanbrc.mm"

theorem mat0dimcrng
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  assume mat0dim.a: |- A = ( (/) Mat R )


  assert |- ( R e. Ring -> A e. CRing )

  proof
    cR
    crg
    wcel
    #
    cA
    crg
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cA
    cmulr
    cfv
    #
    co
    #
    @3
    @2
    @4
    co
    #
    wceq
    #
    vy
    cA
    cbs
    cfv
    #
    wral
    #
    vx
    @8
    wral
    #
    cA
    ccrg
    wcel
    c0
    cfn
    wcel
    @0
    @1
    0fin
    cA
    cR
    c0
    mat0dim.a
    matring
    mpan
    c0
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    c0
    csn
    #
    wceq
    #
    @0
    @10
    cR
    crg
    mat0dimbas0
    @14
    @8
    @13
    wceq
    #
    @0
    @10
    wi
    @12
    @8
    @13
    @11
    cA
    cbs
    cA
    @11
    mat0dim.a
    eqcomi
    fveq2i
    eqeq1i
    @15
    @0
    @10
    @15
    @0
    wa
    #
    @10
    @7
    vy
    @13
    wral
    #
    vx
    @13
    wral
    #
    @16
    c0
    c0
    @4
    co
    #
    @19
    wceq
    #
    @18
    @16
    @19
    eqidd
    @18
    c0
    @3
    @4
    co
    #
    @3
    c0
    @4
    co
    #
    wceq
    #
    vy
    @13
    wral
    #
    @20
    @17
    @24
    vx
    c0
    0ex
    @2
    c0
    wceq
    #
    @7
    @23
    vy
    @13
    @25
    @5
    @21
    @6
    @22
    @2
    c0
    @3
    @4
    oveq1
    @2
    c0
    @3
    @4
    oveq2
    eqeq12d
    ralbidv
    ralsn
    @23
    @20
    vy
    c0
    0ex
    @3
    c0
    wceq
    @21
    @19
    @22
    @19
    @3
    c0
    c0
    @4
    oveq2
    @3
    c0
    c0
    @4
    oveq1
    eqeq12d
    ralsn
    bitri
    sylibr
    @15
    @10
    @18
    wb
    @0
    @9
    @17
    vx
    @8
    @13
    @7
    vy
    @8
    @13
    raleq
    raleqbi1dv
    adantr
    mpbird
    ex
    sylbi
    mpcom
    vx
    vy
    @8
    cA
    @4
    @8
    eqid
    @4
    eqid
    iscrng2
    sylanbrc
end
