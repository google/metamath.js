include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "cima.mm"
include "c1.mm"
include "cfzo.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cfv.mm"
include "wnel.mm"
include "wfn.mm"
include "ffn.mm"
include "adantr.mm"
include "cle.mm"
include "wbr.mm"
include "0nn0.mm"
include "a1i.mm"
include "simpr.mm"
include "nn0ge0.mm"
include "adantl.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "id.mm"
include "nn0re.mm"
include "leidd.mm"
include "fnimapr.mm"
include "syl3anc.mm"
include "ineq1d.mm"
include "eqeq1d.mm"
include "cv.mm"
include "wn.mm"
include "wral.mm"
include "disj.mm"
include "fvex.mm"
include "eleq1.mm"
include "notbid.mm"
include "df-nel.mm"
include "syl6bbr.mm"
include "ralpr.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem fvinim0ffz
  let cF: class F
  let cK: class K
  let cV: class V
  let vv: setvar v


  assert |- ( ( F : ( 0 ... K ) --> V /\ K e. NN0 ) -> ( ( ( F " { 0 , K } ) i^i ( F " ( 1 ..^ K ) ) ) = (/) <-> ( ( F ` 0 ) e/ ( F " ( 1 ..^ K ) ) /\ ( F ` K ) e/ ( F " ( 1 ..^ K ) ) ) ) )

  proof
    cc0
    cK
    cfz
    co
    #
    cV
    cF
    wf
    #
    cK
    cn0
    wcel
    #
    wa
    #
    cF
    cc0
    cK
    cpr
    cima
    #
    cF
    c1
    cK
    cfzo
    co
    cima
    #
    cin
    #
    c0
    wceq
    cc0
    cF
    cfv
    #
    cK
    cF
    cfv
    #
    cpr
    #
    @5
    cin
    #
    c0
    wceq
    #
    @7
    @5
    wnel
    #
    @8
    @5
    wnel
    #
    wa
    #
    @3
    @6
    @10
    c0
    @3
    @4
    @9
    @5
    @3
    cF
    @0
    wfn
    #
    cc0
    @0
    wcel
    #
    cK
    @0
    wcel
    #
    @4
    @9
    wceq
    @1
    @15
    @2
    @0
    cV
    cF
    ffn
    adantr
    @3
    cc0
    cn0
    wcel
    #
    @2
    cc0
    cK
    cle
    wbr
    #
    @16
    @18
    @3
    0nn0
    a1i
    @1
    @2
    simpr
    @2
    @19
    @1
    cK
    nn0ge0
    adantl
    cc0
    cK
    elfz2nn0
    syl3anbrc
    @2
    @17
    @1
    @2
    @2
    @2
    cK
    cK
    cle
    wbr
    @17
    @2
    id
    #
    @20
    @2
    cK
    cK
    nn0re
    leidd
    cK
    cK
    elfz2nn0
    syl3anbrc
    adantl
    @0
    cc0
    cK
    cF
    fnimapr
    syl3anc
    ineq1d
    eqeq1d
    @11
    vv
    cv
    #
    @5
    wcel
    #
    wn
    #
    vv
    @9
    wral
    @14
    vv
    @9
    @5
    disj
    @23
    @12
    @13
    vv
    @7
    @8
    cc0
    cF
    fvex
    cK
    cF
    fvex
    @21
    @7
    wceq
    #
    @23
    @7
    @5
    wcel
    #
    wn
    @12
    @24
    @22
    @25
    @21
    @7
    @5
    eleq1
    notbid
    @7
    @5
    df-nel
    syl6bbr
    @21
    @8
    wceq
    #
    @23
    @8
    @5
    wcel
    #
    wn
    @13
    @26
    @22
    @27
    @21
    @8
    @5
    eleq1
    notbid
    @8
    @5
    df-nel
    syl6bbr
    ralpr
    bitri
    syl6bb
end
