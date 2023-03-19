include "crg.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cur.mm"
include "cfv.mm"
include "cmg.mm"
include "co.mm"
include "wceq.mm"
include "cod.mm"
include "eqid.mm"
include "chrval.mm"
include "breq1i.mm"
include "cgrp.mm"
include "cbs.mm"
include "wb.mm"
include "ringgrp.mm"
include "adantr.mm"
include "ringidcl.mm"
include "simpr.mm"
include "oddvds.mm"
include "syl3anc.mm"
include "syl5bbr.mm"
include "zrhmulg.mm"
include "eqeq1d.mm"
include "bitr4d.mm"

theorem chrdvds
  let cC: class C
  let cR: class R
  let cL: class L
  let cN: class N
  let c.0: class .0.
  assume chrcl.c: |- C = ( chr ` R )
  assume chrid.l: |- L = ( ZRHom ` R )
  assume chrid.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Ring /\ N e. ZZ ) -> ( C || N <-> ( L ` N ) = .0. ) )

  proof
    cR
    crg
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cC
    cN
    cdvds
    wbr
    #
    cN
    cR
    cur
    cfv
    #
    cR
    cmg
    cfv
    #
    co
    #
    c.0
    wceq
    #
    cN
    cL
    cfv
    #
    c.0
    wceq
    @3
    @4
    cR
    cod
    cfv
    #
    cfv
    #
    cN
    cdvds
    wbr
    #
    @2
    @7
    @10
    cC
    cN
    cdvds
    cC
    cR
    @4
    @9
    @9
    eqid
    #
    @4
    eqid
    #
    chrcl.c
    chrval
    breq1i
    @2
    cR
    cgrp
    wcel
    #
    @4
    cR
    cbs
    cfv
    #
    wcel
    #
    @1
    @11
    @7
    wb
    @0
    @14
    @1
    cR
    ringgrp
    adantr
    @0
    @16
    @1
    @15
    cR
    @4
    @15
    eqid
    #
    @13
    ringidcl
    adantr
    @0
    @1
    simpr
    @4
    @5
    cR
    cN
    @9
    @15
    c.0
    @17
    @12
    @5
    eqid
    #
    chrid.z
    oddvds
    syl3anc
    syl5bbr
    @2
    @8
    @6
    c.0
    cR
    @5
    @4
    cL
    cN
    chrid.l
    @18
    @13
    zrhmulg
    eqeq1d
    bitr4d
end
