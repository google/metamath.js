include "ccyg.mm"
include "wcel.mm"
include "cgrp.mm"
include "cz.mm"
include "cv.mm"
include "cmg.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "crab.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cfn.mm"
include "chash.mm"
include "cc0.mm"
include "cif.mm"
include "eqid.mm"
include "iscyg2.mm"
include "wex.mm"
include "n0.mm"
include "cod.mm"
include "ssrab2.mm"
include "simpr.mm"
include "sseldi.mm"
include "cyggenod2.mm"
include "jca.mm"
include "ex.mm"
include "cn0.mm"
include "cdvds.mm"
include "wbr.mm"
include "gexcl.mm"
include "adantr.mm"
include "hashcl.mm"
include "adantl.mm"
include "wn.mm"
include "0nn0.mm"
include "a1i.mm"
include "ifclda.mm"
include "breq2.mm"
include "gexdvds3.mm"
include "adantlr.mm"
include "nn0z.mm"
include "dvds0.mm"
include "3syl.mm"
include "ifbothda.mm"
include "simprr.mm"
include "gexod.mm"
include "adantrr.mm"
include "eqbrtrrd.mm"
include "dvdseq.mm"
include "syl22anc.mm"
include "syld.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "imp.mm"
include "sylbi.mm"

theorem cyggex2
  let cB: class B
  let cE: class E
  let cG: class G
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let cH: class H
  assume cygctb.1: |- B = ( Base ` G )
  assume cyggex.o: |- E = ( gEx ` G )


  assert |- ( G e. CycGrp -> E = if ( B e. Fin , ( # ` B ) , 0 ) )

  proof
    cG
    ccyg
    wcel
    cG
    cgrp
    wcel
    #
    vn
    cz
    vn
    cv
    vx
    cv
    cG
    cmg
    cfv
    #
    co
    cmpt
    crn
    cB
    wceq
    #
    vx
    cB
    crab
    #
    c0
    wne
    #
    wa
    cE
    cB
    cfn
    wcel
    #
    cB
    chash
    cfv
    #
    cc0
    cif
    #
    wceq
    #
    vx
    cB
    @1
    vn
    @3
    cG
    cygctb.1
    @1
    eqid
    #
    @3
    eqid
    #
    iscyg2
    @0
    @4
    @8
    @4
    vy
    cv
    #
    @3
    wcel
    #
    vy
    wex
    @0
    @8
    vy
    @3
    n0
    @0
    @12
    @8
    vy
    @0
    @12
    @11
    cB
    wcel
    #
    @11
    cG
    cod
    cfv
    #
    cfv
    #
    @7
    wceq
    #
    wa
    #
    @8
    @0
    @12
    @17
    @0
    @12
    wa
    #
    @13
    @16
    @18
    @3
    cB
    @11
    @2
    vx
    cB
    ssrab2
    @0
    @12
    simpr
    sseldi
    vx
    cB
    @1
    vn
    @3
    cG
    @14
    @11
    cygctb.1
    @9
    @10
    @14
    eqid
    #
    cyggenod2
    jca
    ex
    @0
    @17
    @8
    @0
    @17
    wa
    #
    cE
    cn0
    wcel
    #
    @7
    cn0
    wcel
    cE
    @7
    cdvds
    wbr
    #
    @7
    cE
    cdvds
    wbr
    @8
    @0
    @21
    @17
    cE
    cG
    cgrp
    cB
    cygctb.1
    cyggex.o
    gexcl
    adantr
    #
    @20
    @5
    @6
    cc0
    cn0
    @5
    @6
    cn0
    wcel
    @20
    cB
    hashcl
    adantl
    cc0
    cn0
    wcel
    @20
    @5
    wn
    #
    wa
    #
    0nn0
    a1i
    ifclda
    @5
    cE
    @6
    cdvds
    wbr
    #
    cE
    cc0
    cdvds
    wbr
    #
    @22
    @20
    @6
    cc0
    @6
    @7
    cE
    cdvds
    breq2
    cc0
    @7
    cE
    cdvds
    breq2
    @0
    @5
    @26
    @17
    cE
    cG
    cB
    cygctb.1
    cyggex.o
    gexdvds3
    adantlr
    @25
    @21
    cE
    cz
    wcel
    @27
    @20
    @21
    @24
    @23
    adantr
    cE
    nn0z
    cE
    dvds0
    3syl
    ifbothda
    @20
    @15
    @7
    cE
    cdvds
    @0
    @13
    @16
    simprr
    @0
    @13
    @15
    cE
    cdvds
    wbr
    @16
    @11
    cE
    cG
    @14
    cB
    cygctb.1
    cyggex.o
    @19
    gexod
    adantrr
    eqbrtrrd
    cE
    @7
    dvdseq
    syl22anc
    ex
    syld
    exlimdv
    syl5bi
    imp
    sylbi
end
