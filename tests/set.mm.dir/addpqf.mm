include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cmi.mm"
include "co.mm"
include "cpli.mm"
include "cop.mm"
include "cnpi.mm"
include "cxp.mm"
include "wcel.mm"
include "wral.mm"
include "cplpq.mm"
include "wf.mm"
include "wa.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "mulclpi.mm"
include "syl2an.mm"
include "syl2anr.mm"
include "addclpi.mm"
include "syl2anc.mm"
include "opelxpi.mm"
include "rgen2a.mm"
include "df-plpq.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem addpqf
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- +pQ : ( ( N. X. N. ) X. ( N. X. N. ) ) --> ( N. X. N. )

  proof
    vx
    cv
    #
    c1st
    cfv
    #
    vy
    cv
    #
    c2nd
    cfv
    #
    cmi
    co
    #
    @2
    c1st
    cfv
    #
    @0
    c2nd
    cfv
    #
    cmi
    co
    #
    cpli
    co
    #
    @6
    @3
    cmi
    co
    #
    cop
    #
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    vy
    @11
    wral
    vx
    @11
    wral
    @11
    @11
    cxp
    @11
    cplpq
    wf
    @12
    vx
    vy
    @11
    @0
    @11
    wcel
    #
    @2
    @11
    wcel
    #
    wa
    #
    @8
    cnpi
    wcel
    #
    @9
    cnpi
    wcel
    #
    @12
    @15
    @4
    cnpi
    wcel
    #
    @7
    cnpi
    wcel
    #
    @16
    @13
    @1
    cnpi
    wcel
    @3
    cnpi
    wcel
    #
    @18
    @14
    @0
    cnpi
    cnpi
    xp1st
    @2
    cnpi
    cnpi
    xp2nd
    #
    @1
    @3
    mulclpi
    syl2an
    @14
    @5
    cnpi
    wcel
    @6
    cnpi
    wcel
    #
    @19
    @13
    @2
    cnpi
    cnpi
    xp1st
    @0
    cnpi
    cnpi
    xp2nd
    #
    @5
    @6
    mulclpi
    syl2anr
    @4
    @7
    addclpi
    syl2anc
    @13
    @22
    @20
    @17
    @14
    @23
    @21
    @6
    @3
    mulclpi
    syl2an
    @8
    @9
    cnpi
    cnpi
    opelxpi
    syl2anc
    rgen2a
    vx
    vy
    @11
    @11
    @10
    @11
    cplpq
    vx
    vy
    df-plpq
    fmpt2
    mpbi
end
