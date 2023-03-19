include "cv.mm"
include "cop.mm"
include "cer.mm"
include "cec.mm"
include "c0r.mm"
include "cmr.mm"
include "co.mm"
include "wceq.mm"
include "cnp.mm"
include "cnr.mm"
include "df-nr.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "wcel.mm"
include "wa.mm"
include "c1p.mm"
include "cmp.mm"
include "cpp.mm"
include "1pr.mm"
include "mulsrpr.mm"
include "mpanr12.mm"
include "mulclpr.mm"
include "mpan2.mm"
include "addclpr.mm"
include "syl2an.mm"
include "anim12i.mm"
include "eqid.mm"
include "enreceq.mm"
include "mpbiri.mm"
include "sylan.mm"
include "anidms.mm"
include "eqtrd.mm"
include "df-0r.mm"
include "oveq2i.mm"
include "3eqtr4g.mm"
include "ecoptocl.mm"

theorem 00sr
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. R. -> ( A .R 0R ) = 0R )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cop
    cer
    cec
    #
    c0r
    cmr
    co
    #
    c0r
    wceq
    cA
    c0r
    cmr
    co
    #
    c0r
    wceq
    vx
    vy
    cA
    cnp
    cnp
    cer
    cnr
    df-nr
    @2
    cA
    wceq
    @3
    @4
    c0r
    @2
    cA
    c0r
    cmr
    oveq1
    eqeq1d
    @0
    cnp
    wcel
    #
    @1
    cnp
    wcel
    #
    wa
    #
    @2
    c1p
    c1p
    cop
    cer
    cec
    #
    cmr
    co
    #
    @8
    @3
    c0r
    @7
    @9
    @0
    c1p
    cmp
    co
    #
    @1
    c1p
    cmp
    co
    #
    cpp
    co
    #
    @12
    cop
    cer
    cec
    #
    @8
    @7
    c1p
    cnp
    wcel
    #
    @14
    @9
    @13
    wceq
    1pr
    1pr
    @0
    @1
    c1p
    c1p
    mulsrpr
    mpanr12
    @7
    @13
    @8
    wceq
    #
    @7
    @7
    wa
    #
    @14
    @14
    @15
    1pr
    1pr
    @16
    @12
    cnp
    wcel
    #
    @17
    wa
    #
    @14
    @14
    wa
    #
    @15
    @7
    @17
    @7
    @17
    @5
    @10
    cnp
    wcel
    #
    @11
    cnp
    wcel
    #
    @17
    @6
    @5
    @14
    @20
    1pr
    @0
    c1p
    mulclpr
    mpan2
    @6
    @14
    @21
    1pr
    @1
    c1p
    mulclpr
    mpan2
    @10
    @11
    addclpr
    syl2an
    #
    @22
    anim12i
    @18
    @19
    wa
    @15
    @12
    c1p
    cpp
    co
    #
    @23
    wceq
    @23
    eqid
    @12
    @12
    c1p
    c1p
    enreceq
    mpbiri
    sylan
    mpanr12
    anidms
    eqtrd
    c0r
    @8
    @2
    cmr
    df-0r
    oveq2i
    df-0r
    3eqtr4g
    ecoptocl
end
