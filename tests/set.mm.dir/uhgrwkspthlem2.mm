include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "c1.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "cc0.mm"
include "ccnv.mm"
include "wfun.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf.mm"
include "wi.mm"
include "eqid.mm"
include "wlkp.mm"
include "cpr.mm"
include "wb.mm"
include "oveq2.mm"
include "caddc.mm"
include "1e0p1.mm"
include "oveq2i.mm"
include "cz.mm"
include "wcel.mm"
include "0z.mm"
include "fzpr.mm"
include "ax-mp.mm"
include "0p1e1.mm"
include "preq2i.mm"
include "3eqtri.mm"
include "syl6eq.mm"
include "feq2d.mm"
include "adantr.mm"
include "simpl.mm"
include "simpr.mm"
include "neeq12d.mm"
include "bicomd.mm"
include "fveq2.mm"
include "neeq2d.mm"
include "sylan9bbr.mm"
include "anbi12d.mm"
include "cop.mm"
include "w3a.mm"
include "1z.mm"
include "fpr2g.mm"
include "mp2an.mm"
include "cs2.mm"
include "funcnvs2.mm"
include "3expa.mm"
include "adantl.mm"
include "s2prop.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "cnveqd.mm"
include "funeqd.mm"
include "mpbird.mm"
include "exp32.mm"
include "impcom.mm"
include "3impa.mm"
include "sylbi.mm"
include "imp.mm"
include "syl6bi.mm"
include "expd.mm"
include "com12.mm"
include "com34.mm"
include "impd.mm"
include "syl.mm"
include "3imp.mm"

theorem uhgrwkspthlem2
  let cA: class A
  let cB: class B
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( ( F ( Walks ` G ) P /\ ( ( # ` F ) = 1 /\ A =/= B ) /\ ( ( P ` 0 ) = A /\ ( P ` ( # ` F ) ) = B ) ) -> Fun `' P )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    chash
    cfv
    #
    c1
    wceq
    #
    cA
    cB
    wne
    #
    wa
    #
    cc0
    cP
    cfv
    #
    cA
    wceq
    #
    @1
    cP
    cfv
    #
    cB
    wceq
    #
    wa
    #
    cP
    ccnv
    #
    wfun
    #
    @0
    cc0
    @1
    cfz
    co
    #
    cG
    cvtx
    cfv
    #
    cP
    wf
    #
    @4
    @9
    @11
    wi
    #
    wi
    cP
    cF
    cG
    @13
    @13
    eqid
    wlkp
    @14
    @2
    @3
    @15
    @14
    @2
    @9
    @3
    @11
    @14
    @2
    @9
    @3
    @11
    wi
    #
    @2
    @9
    wa
    #
    @14
    @16
    @17
    @14
    @3
    @11
    @17
    @14
    @3
    wa
    cc0
    c1
    cpr
    #
    @13
    cP
    wf
    #
    @5
    c1
    cP
    cfv
    #
    wne
    #
    wa
    @11
    @17
    @14
    @19
    @3
    @21
    @2
    @14
    @19
    wb
    @9
    @2
    @12
    @18
    @13
    cP
    @2
    @12
    cc0
    c1
    cfz
    co
    #
    @18
    @1
    c1
    cc0
    cfz
    oveq2
    @22
    cc0
    cc0
    c1
    caddc
    co
    #
    cfz
    co
    #
    cc0
    @23
    cpr
    #
    @18
    c1
    @23
    cc0
    cfz
    1e0p1
    oveq2i
    cc0
    cz
    wcel
    #
    @24
    @25
    wceq
    0z
    cc0
    fzpr
    ax-mp
    @23
    c1
    cc0
    0p1e1
    preq2i
    3eqtri
    syl6eq
    feq2d
    adantr
    @9
    @3
    @5
    @7
    wne
    #
    @2
    @21
    @9
    @27
    @3
    @9
    @5
    cA
    @7
    cB
    @6
    @8
    simpl
    @6
    @8
    simpr
    neeq12d
    bicomd
    @2
    @7
    @20
    @5
    @1
    c1
    cP
    fveq2
    neeq2d
    sylan9bbr
    anbi12d
    @19
    @21
    @11
    @19
    @5
    @13
    wcel
    #
    @20
    @13
    wcel
    #
    cP
    cc0
    @5
    cop
    c1
    @20
    cop
    cpr
    #
    wceq
    #
    w3a
    #
    @21
    @11
    wi
    #
    @26
    c1
    cz
    wcel
    @19
    @32
    wb
    0z
    1z
    cc0
    c1
    @13
    cP
    cz
    cz
    fpr2g
    mp2an
    @28
    @29
    @31
    @33
    @31
    @28
    @29
    wa
    #
    @33
    @31
    @34
    @21
    @11
    @31
    @34
    @21
    wa
    #
    wa
    #
    @11
    @5
    @20
    cs2
    #
    ccnv
    #
    wfun
    #
    @35
    @39
    @31
    @28
    @29
    @21
    @39
    @5
    @20
    @13
    funcnvs2
    3expa
    adantl
    @36
    @10
    @38
    @36
    cP
    @37
    @36
    cP
    @30
    @37
    @31
    @35
    simpl
    @35
    @30
    @37
    wceq
    #
    @31
    @34
    @40
    @21
    @34
    @37
    @30
    @5
    @20
    @13
    s2prop
    eqcomd
    adantr
    adantl
    eqtrd
    cnveqd
    funeqd
    mpbird
    exp32
    impcom
    3impa
    sylbi
    imp
    syl6bi
    expd
    com12
    expd
    com34
    impd
    syl
    3imp
end
