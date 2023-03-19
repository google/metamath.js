include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "clt.mm"
include "wbr.mm"
include "cpnf.mm"
include "cmnf.mm"
include "cmul.mm"
include "co.mm"
include "cif.mm"
include "cxmu.mm"
include "wn.mm"
include "wne.mm"
include "renepnf.mm"
include "adantr.mm"
include "necon2bi.mm"
include "adantl.mm"
include "renemnf.mm"
include "jaoi.mm"
include "con2i.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "ifeq2d.mm"
include "cxr.mm"
include "rexr.mm"
include "xmulval.mm"
include "syl2an.mm"
include "ifid.mm"
include "oveq1.mm"
include "mul02lem2.mm"
include "sylan9eqr.mm"
include "oveq2.mm"
include "recn.mm"
include "mul01d.mm"
include "jaodan.mm"
include "ifeq1da.mm"
include "syl5eqr.mm"
include "3eqtr4d.mm"

theorem rexmul
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A *e B ) = ( A x. B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    wo
    #
    cc0
    cc0
    cB
    clt
    wbr
    #
    cA
    cpnf
    wceq
    #
    wa
    #
    cB
    cc0
    clt
    wbr
    #
    cA
    cmnf
    wceq
    #
    wa
    #
    wo
    #
    cc0
    cA
    clt
    wbr
    #
    cB
    cpnf
    wceq
    #
    wa
    #
    cA
    cc0
    clt
    wbr
    #
    cB
    cmnf
    wceq
    #
    wa
    #
    wo
    #
    wo
    #
    cpnf
    @6
    @10
    wa
    #
    @9
    @7
    wa
    #
    wo
    #
    @13
    @17
    wa
    #
    @16
    @14
    wa
    #
    wo
    #
    wo
    #
    cmnf
    cA
    cB
    cmul
    co
    #
    cif
    #
    cif
    #
    cif
    #
    @5
    cc0
    @28
    cif
    #
    cA
    cB
    cxmu
    co
    #
    @28
    @2
    @5
    @30
    @28
    cc0
    @2
    @30
    @29
    @28
    @2
    @20
    cpnf
    @29
    @20
    @2
    @12
    @2
    wn
    #
    @19
    @8
    @34
    @11
    @7
    @34
    @6
    @2
    cA
    cpnf
    @0
    cA
    cpnf
    wne
    @1
    cA
    renepnf
    adantr
    necon2bi
    #
    adantl
    @10
    @34
    @9
    @2
    cA
    cmnf
    @0
    cA
    cmnf
    wne
    @1
    cA
    renemnf
    adantr
    necon2bi
    #
    adantl
    jaoi
    @15
    @34
    @18
    @14
    @34
    @13
    @2
    cB
    cpnf
    @1
    cB
    cpnf
    wne
    @0
    cB
    renepnf
    adantl
    necon2bi
    #
    adantl
    @17
    @34
    @16
    @2
    cB
    cmnf
    @1
    cB
    cmnf
    wne
    @0
    cB
    renemnf
    adantl
    necon2bi
    #
    adantl
    jaoi
    jaoi
    con2i
    iffalsed
    @2
    @27
    cmnf
    @28
    @27
    @2
    @23
    @34
    @26
    @21
    @34
    @22
    @10
    @34
    @6
    @36
    adantl
    @7
    @34
    @9
    @35
    adantl
    jaoi
    @24
    @34
    @25
    @17
    @34
    @13
    @38
    adantl
    @14
    @34
    @16
    @37
    adantl
    jaoi
    jaoi
    con2i
    iffalsed
    eqtrd
    ifeq2d
    @0
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @33
    @31
    wceq
    @1
    cA
    rexr
    cB
    rexr
    cA
    cB
    xmulval
    syl2an
    @2
    @28
    @5
    @28
    @28
    cif
    @32
    @5
    @28
    ifid
    @2
    @5
    @28
    cc0
    @28
    @2
    @3
    @28
    cc0
    wceq
    @4
    @3
    @2
    @28
    cc0
    cB
    cmul
    co
    #
    cc0
    cA
    cc0
    cB
    cmul
    oveq1
    @1
    @39
    cc0
    wceq
    @0
    cB
    mul02lem2
    adantl
    sylan9eqr
    @4
    @2
    @28
    cA
    cc0
    cmul
    co
    #
    cc0
    cB
    cc0
    cA
    cmul
    oveq2
    @0
    @40
    cc0
    wceq
    @1
    @0
    cA
    cA
    recn
    mul01d
    adantr
    sylan9eqr
    jaodan
    ifeq1da
    syl5eqr
    3eqtr4d
end
