include "wfr.mm"
include "wse.mm"
include "wa.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cpred.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "frss.mm"
include "sess2.mm"
include "anim12d.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "predeq3.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "ex.mm"
include "adantl.mm"
include "ctrpred.mm"
include "cvv.mm"
include "setlikespec.mm"
include "trpredpred.mm"
include "ssn0.mm"
include "syl.mm"
include "trpredss.mm"
include "jctild.mm"
include "adantr.mm"
include "trpredex.mm"
include "sseq1.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "predeq2.mm"
include "rexeqbi1dv.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "wal.mm"
include "dffr4.mm"
include "sp.mm"
include "sylbi.mm"
include "vtocl.mm"
include "trpredtr.mm"
include "imp.mm"
include "sspred.mm"
include "syl2anc.mm"
include "biimprd.mm"
include "reximdva.mm"
include "ssrexv.mm"
include "sylsyld.mm"
include "sylan9r.mm"
include "syld.mm"
include "an31s.mm"
include "pm2.61dne.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "syl6com.mm"
include "imp32.mm"

theorem frmin
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let vb: setvar b
  let vc: setvar c

  disjoint B y
  disjoint R y
  disjoint A b
  disjoint B b
  disjoint B c
  disjoint b c
  disjoint b y
  disjoint c y
  disjoint R b
  disjoint R c
  assert |- ( ( ( R Fr A /\ R Se A ) /\ ( B C_ A /\ B =/= (/) ) ) -> E. y e. B Pred ( R , B , y ) = (/) )

  proof
    cA
    cR
    wfr
    #
    cA
    cR
    wse
    #
    wa
    #
    cB
    cA
    wss
    #
    cB
    c0
    wne
    #
    cB
    cR
    vy
    cv
    #
    cpred
    #
    c0
    wceq
    #
    vy
    cB
    wrex
    #
    @3
    @2
    cB
    cR
    wfr
    #
    cB
    cR
    wse
    #
    wa
    #
    @4
    @8
    wi
    @3
    @0
    @9
    @1
    @10
    cB
    cA
    cR
    frss
    cB
    cA
    cR
    sess2
    anim12d
    @4
    vb
    cv
    #
    cB
    wcel
    #
    vb
    wex
    @11
    @8
    vb
    cB
    n0
    @11
    @13
    @8
    vb
    @11
    @13
    @8
    @11
    @13
    wa
    @8
    cB
    cR
    @12
    cpred
    #
    c0
    @13
    @14
    c0
    wceq
    #
    @8
    wi
    @11
    @13
    @15
    @8
    @7
    @15
    vy
    @12
    cB
    @5
    @12
    wceq
    @6
    @14
    c0
    cB
    cR
    @5
    @12
    predeq3
    eqeq1d
    rspcev
    ex
    adantl
    @13
    @10
    @9
    @14
    c0
    wne
    #
    @8
    wi
    @13
    @10
    wa
    #
    @9
    wa
    @16
    cB
    cR
    @12
    ctrpred
    #
    cB
    wss
    #
    @18
    c0
    wne
    #
    wa
    #
    @8
    @17
    @16
    @21
    wi
    #
    @9
    @17
    @14
    cvv
    wcel
    #
    @22
    cB
    cR
    @12
    setlikespec
    #
    @23
    @16
    @20
    @19
    @23
    @14
    @18
    wss
    #
    @16
    @20
    wi
    cB
    cvv
    cR
    @12
    trpredpred
    @25
    @16
    @20
    @14
    @18
    ssn0
    ex
    syl
    cB
    cvv
    cR
    @12
    trpredss
    #
    jctild
    syl
    adantr
    @9
    @21
    @18
    cR
    @5
    cpred
    #
    c0
    wceq
    #
    vy
    @18
    wrex
    #
    @17
    @8
    @9
    vc
    cv
    #
    cB
    wss
    #
    @30
    c0
    wne
    #
    wa
    #
    @30
    cR
    @5
    cpred
    #
    c0
    wceq
    #
    vy
    @30
    wrex
    #
    wi
    #
    wi
    @9
    @21
    @29
    wi
    #
    wi
    vc
    @18
    cB
    cR
    @12
    trpredex
    @30
    @18
    wceq
    #
    @37
    @38
    @9
    @39
    @33
    @21
    @36
    @29
    @39
    @31
    @19
    @32
    @20
    @30
    @18
    cB
    sseq1
    @30
    @18
    c0
    neeq1
    anbi12d
    @35
    @28
    vy
    @30
    @18
    @39
    @34
    @27
    c0
    @30
    @18
    cR
    @5
    predeq2
    eqeq1d
    rexeqbi1dv
    imbi12d
    imbi2d
    @9
    @37
    vc
    wal
    @37
    vc
    vy
    cB
    cR
    dffr4
    @37
    vc
    sp
    sylbi
    vtocl
    @17
    @19
    @29
    @7
    vy
    @18
    wrex
    @8
    @17
    @23
    @19
    @24
    @26
    syl
    #
    @17
    @28
    @7
    vy
    @18
    @17
    @5
    @18
    wcel
    #
    wa
    #
    @7
    @28
    @42
    @6
    @27
    c0
    @42
    @19
    @6
    @18
    wss
    #
    @6
    @27
    wceq
    @17
    @19
    @41
    @40
    adantr
    @17
    @41
    @43
    cB
    cR
    @12
    @5
    trpredtr
    imp
    cB
    @18
    cR
    @5
    sspred
    syl2anc
    eqeq1d
    biimprd
    reximdva
    @7
    vy
    @18
    cB
    ssrexv
    sylsyld
    sylan9r
    syld
    an31s
    pm2.61dne
    ex
    exlimdv
    syl5bi
    syl6com
    imp32
end
