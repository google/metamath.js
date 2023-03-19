include "cnr.mm"
include "wcel.mm"
include "wa.mm"
include "cmr.mm"
include "co.mm"
include "cnp.mm"
include "cxp.mm"
include "cer.mm"
include "cqs.mm"
include "cv.mm"
include "cop.mm"
include "cec.mm"
include "df-nr.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "cmp.mm"
include "cpp.mm"
include "mulsrpr.mm"
include "mulclpr.mm"
include "addclpr.mm"
include "syl2an.mm"
include "an4s.mm"
include "an42s.mm"
include "jca.mm"
include "opelxpi.mm"
include "enrex.mm"
include "ecelqsi.mm"
include "3syl.mm"
include "eqeltrd.mm"
include "2ecoptocl.mm"
include "syl6eleqr.mm"

theorem mulclsr
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( A e. R. /\ B e. R. ) -> ( A .R B ) e. R. )

  proof
    cA
    cnr
    wcel
    cB
    cnr
    wcel
    wa
    cA
    cB
    cmr
    co
    #
    cnp
    cnp
    cxp
    #
    cer
    cqs
    #
    cnr
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
    vz
    cv
    #
    vw
    cv
    #
    cop
    cer
    cec
    #
    cmr
    co
    #
    @2
    wcel
    cA
    @8
    cmr
    co
    #
    @2
    wcel
    @0
    @2
    wcel
    vx
    vy
    vz
    vw
    cA
    cB
    cnp
    cnp
    cer
    cnr
    df-nr
    @5
    cA
    wceq
    @9
    @10
    @2
    @5
    cA
    @8
    cmr
    oveq1
    eleq1d
    @8
    cB
    wceq
    @10
    @0
    @2
    @8
    cB
    cA
    cmr
    oveq2
    eleq1d
    @3
    cnp
    wcel
    #
    @4
    cnp
    wcel
    #
    wa
    @6
    cnp
    wcel
    #
    @7
    cnp
    wcel
    #
    wa
    wa
    #
    @9
    @3
    @6
    cmp
    co
    #
    @4
    @7
    cmp
    co
    #
    cpp
    co
    #
    @3
    @7
    cmp
    co
    #
    @4
    @6
    cmp
    co
    #
    cpp
    co
    #
    cop
    #
    cer
    cec
    #
    @2
    @3
    @4
    @6
    @7
    mulsrpr
    @15
    @18
    cnp
    wcel
    #
    @21
    cnp
    wcel
    #
    wa
    @22
    @1
    wcel
    @23
    @2
    wcel
    @15
    @24
    @25
    @11
    @13
    @12
    @14
    @24
    @11
    @13
    wa
    @16
    cnp
    wcel
    @17
    cnp
    wcel
    @24
    @12
    @14
    wa
    @3
    @6
    mulclpr
    @4
    @7
    mulclpr
    @16
    @17
    addclpr
    syl2an
    an4s
    @11
    @14
    @12
    @13
    @25
    @11
    @14
    wa
    @19
    cnp
    wcel
    @20
    cnp
    wcel
    @25
    @12
    @13
    wa
    @3
    @7
    mulclpr
    @4
    @6
    mulclpr
    @19
    @20
    addclpr
    syl2an
    an42s
    jca
    @18
    @21
    cnp
    cnp
    opelxpi
    @1
    @22
    cer
    enrex
    ecelqsi
    3syl
    eqeltrd
    2ecoptocl
    df-nr
    syl6eleqr
end
