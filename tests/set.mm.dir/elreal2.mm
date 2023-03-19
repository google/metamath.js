include "cr.mm"
include "wcel.mm"
include "cnr.mm"
include "c0r.mm"
include "csn.mm"
include "cxp.mm"
include "c1st.mm"
include "cfv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "df-r.mm"
include "eleq2i.mm"
include "xp1st.mm"
include "c2nd.mm"
include "1st2nd2.mm"
include "xp2nd.mm"
include "elsni.mm"
include "syl.mm"
include "opeq2d.mm"
include "eqtrd.mm"
include "jca.mm"
include "eleq1.mm"
include "0r.mm"
include "elexi.mm"
include "snid.mm"
include "opelxp.mm"
include "mpbiran2.mm"
include "syl6bb.mm"
include "biimparc.mm"
include "impbii.mm"
include "bitri.mm"

theorem elreal2
  let cA: class A


  assert |- ( A e. RR <-> ( ( 1st ` A ) e. R. /\ A = <. ( 1st ` A ) , 0R >. ) )

  proof
    cA
    cr
    wcel
    cA
    cnr
    c0r
    csn
    #
    cxp
    #
    wcel
    #
    cA
    c1st
    cfv
    #
    cnr
    wcel
    #
    cA
    @3
    c0r
    cop
    #
    wceq
    #
    wa
    #
    cr
    @1
    cA
    df-r
    eleq2i
    @2
    @7
    @2
    @4
    @6
    cA
    cnr
    @0
    xp1st
    @2
    cA
    @3
    cA
    c2nd
    cfv
    #
    cop
    @5
    cA
    cnr
    @0
    1st2nd2
    @2
    @8
    c0r
    @3
    @2
    @8
    @0
    wcel
    @8
    c0r
    wceq
    cA
    cnr
    @0
    xp2nd
    @8
    c0r
    elsni
    syl
    opeq2d
    eqtrd
    jca
    @6
    @2
    @4
    @6
    @2
    @5
    @1
    wcel
    #
    @4
    cA
    @5
    @1
    eleq1
    @9
    @4
    c0r
    @0
    wcel
    c0r
    c0r
    cnr
    0r
    elexi
    snid
    @3
    c0r
    cnr
    @0
    opelxp
    mpbiran2
    syl6bb
    biimparc
    impbii
    bitri
end
