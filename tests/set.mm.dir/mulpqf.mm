include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "cmi.mm"
include "co.mm"
include "c2nd.mm"
include "cop.mm"
include "cnpi.mm"
include "cxp.mm"
include "wcel.mm"
include "wral.mm"
include "cmpq.mm"
include "wf.mm"
include "wa.mm"
include "xp1st.mm"
include "mulclpi.mm"
include "syl2an.mm"
include "xp2nd.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "rgen2a.mm"
include "df-mpq.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem mulpqf
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- .pQ : ( ( N. X. N. ) X. ( N. X. N. ) ) --> ( N. X. N. )

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
    c1st
    cfv
    #
    cmi
    co
    #
    @0
    c2nd
    cfv
    #
    @2
    c2nd
    cfv
    #
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
    @9
    wral
    vx
    @9
    wral
    @9
    @9
    cxp
    @9
    cmpq
    wf
    @10
    vx
    vy
    @9
    @0
    @9
    wcel
    #
    @2
    @9
    wcel
    #
    wa
    @4
    cnpi
    wcel
    #
    @7
    cnpi
    wcel
    #
    @10
    @11
    @1
    cnpi
    wcel
    @3
    cnpi
    wcel
    @13
    @12
    @0
    cnpi
    cnpi
    xp1st
    @2
    cnpi
    cnpi
    xp1st
    @1
    @3
    mulclpi
    syl2an
    @11
    @5
    cnpi
    wcel
    @6
    cnpi
    wcel
    @14
    @12
    @0
    cnpi
    cnpi
    xp2nd
    @2
    cnpi
    cnpi
    xp2nd
    @5
    @6
    mulclpi
    syl2an
    @4
    @7
    cnpi
    cnpi
    opelxpi
    syl2anc
    rgen2a
    vx
    vy
    @9
    @9
    @8
    @9
    cmpq
    vx
    vy
    df-mpq
    fmpt2
    mpbi
end
