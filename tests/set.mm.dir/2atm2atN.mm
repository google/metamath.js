include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cplt.mm"
include "cfv.mm"
include "wbr.mm"
include "wne.mm"
include "cple.mm"
include "cops.mm"
include "hlop.mm"
include "adantr.mm"
include "simpr3.mm"
include "eqid.mm"
include "0ltat.mm"
include "syl2anc.mm"
include "simpl.mm"
include "simpr1.mm"
include "hlatlej1.mm"
include "syl3anc.mm"
include "simpr2.mm"
include "clat.mm"
include "cbs.mm"
include "wb.mm"
include "hllat.mm"
include "atbase.mm"
include "syl.mm"
include "hlatjcl.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cpo.mm"
include "wi.mm"
include "hlpos.mm"
include "op0cl.mm"
include "latmcl.mm"
include "pltletr.mm"
include "mp2and.mm"
include "opltn0.mm"
include "mpbid.mm"

theorem 2atm2atN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let c.0: class .0.
  assume 2atm2at.j: |- .\/ = ( join ` K )
  assume 2atm2at.m: |- ./\ = ( meet ` K )
  assume 2atm2at.z: |- .0. = ( 0. ` K )
  assume 2atm2at.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) ) -> ( ( R .\/ P ) ./\ ( R .\/ Q ) ) =/= .0. )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    w3a
    #
    wa
    #
    c.0
    cR
    cP
    c.or
    co
    #
    cR
    cQ
    c.or
    co
    #
    c.an
    co
    #
    cK
    cplt
    cfv
    #
    wbr
    #
    @8
    c.0
    wne
    #
    @5
    c.0
    cR
    @9
    wbr
    #
    cR
    @8
    cK
    cple
    cfv
    #
    wbr
    #
    @10
    @5
    cK
    cops
    wcel
    #
    @3
    @12
    @0
    @15
    @4
    cK
    hlop
    adantr
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    cA
    cR
    @9
    cK
    c.0
    2atm2at.z
    @9
    eqid
    #
    2atm2at.a
    0ltat
    syl2anc
    @5
    cR
    @6
    @13
    wbr
    #
    cR
    @7
    @13
    wbr
    #
    @14
    @5
    @0
    @3
    @1
    @19
    @0
    @4
    simpl
    #
    @17
    @0
    @1
    @2
    @3
    simpr1
    #
    cA
    cR
    cP
    c.or
    cK
    @13
    @13
    eqid
    #
    2atm2at.j
    2atm2at.a
    hlatlej1
    syl3anc
    @5
    @0
    @3
    @2
    @20
    @21
    @17
    @0
    @1
    @2
    @3
    simpr2
    #
    cA
    cR
    cQ
    c.or
    cK
    @13
    @23
    2atm2at.j
    2atm2at.a
    hlatlej1
    syl3anc
    @5
    cK
    clat
    wcel
    #
    cR
    cK
    cbs
    cfv
    #
    wcel
    #
    @6
    @26
    wcel
    #
    @7
    @26
    wcel
    #
    @19
    @20
    wa
    @14
    wb
    @0
    @25
    @4
    cK
    hllat
    adantr
    #
    @5
    @3
    @27
    @17
    cA
    @26
    cR
    cK
    @26
    eqid
    #
    2atm2at.a
    atbase
    syl
    #
    @5
    @0
    @3
    @1
    @28
    @21
    @17
    @22
    cA
    @26
    c.or
    cK
    cR
    cP
    @31
    2atm2at.j
    2atm2at.a
    hlatjcl
    syl3anc
    #
    @5
    @0
    @3
    @2
    @29
    @21
    @17
    @24
    cA
    @26
    c.or
    cK
    cR
    cQ
    @31
    2atm2at.j
    2atm2at.a
    hlatjcl
    syl3anc
    #
    @26
    cK
    @13
    c.an
    cR
    @6
    @7
    @31
    @23
    2atm2at.m
    latlem12
    syl13anc
    mpbi2and
    @5
    cK
    cpo
    wcel
    #
    c.0
    @26
    wcel
    #
    @27
    @8
    @26
    wcel
    #
    @12
    @14
    wa
    @10
    wi
    @0
    @35
    @4
    cK
    hlpos
    adantr
    @5
    @15
    @36
    @16
    @26
    cK
    c.0
    @31
    2atm2at.z
    op0cl
    syl
    @32
    @5
    @25
    @28
    @29
    @37
    @30
    @33
    @34
    @26
    cK
    c.an
    @6
    @7
    @31
    2atm2at.m
    latmcl
    syl3anc
    #
    @26
    @9
    cK
    @13
    c.0
    cR
    @8
    @31
    @23
    @18
    pltletr
    syl13anc
    mp2and
    @5
    @15
    @37
    @10
    @11
    wb
    @16
    @38
    @26
    @9
    cK
    @8
    c.0
    @31
    @18
    2atm2at.z
    opltn0
    syl2anc
    mpbid
end
