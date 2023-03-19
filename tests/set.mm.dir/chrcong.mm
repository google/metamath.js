include "crg.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cur.mm"
include "cfv.mm"
include "cmg.mm"
include "wceq.mm"
include "cod.mm"
include "eqid.mm"
include "chrval.mm"
include "breq1i.mm"
include "cgrp.mm"
include "cbs.mm"
include "wb.mm"
include "ringgrp.mm"
include "3ad2ant1.mm"
include "ringidcl.mm"
include "simp2.mm"
include "simp3.mm"
include "odcong.mm"
include "syl112anc.mm"
include "syl5bbr.mm"
include "zrhmulg.mm"
include "3adant3.mm"
include "3adant2.mm"
include "eqeq12d.mm"
include "bitr4d.mm"

theorem chrcong
  let cC: class C
  let cR: class R
  let cL: class L
  let cM: class M
  let cN: class N
  let c.0: class .0.
  assume chrcl.c: |- C = ( chr ` R )
  assume chrid.l: |- L = ( ZRHom ` R )
  assume chrid.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Ring /\ M e. ZZ /\ N e. ZZ ) -> ( C || ( M - N ) <-> ( L ` M ) = ( L ` N ) ) )

  proof
    cR
    crg
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cC
    cM
    cN
    cmin
    co
    #
    cdvds
    wbr
    #
    cM
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
    cN
    @6
    @7
    co
    #
    wceq
    #
    cM
    cL
    cfv
    #
    cN
    cL
    cfv
    #
    wceq
    @5
    @6
    cR
    cod
    cfv
    #
    cfv
    #
    @4
    cdvds
    wbr
    #
    @3
    @10
    @14
    cC
    @4
    cdvds
    cC
    cR
    @6
    @13
    @13
    eqid
    #
    @6
    eqid
    #
    chrcl.c
    chrval
    breq1i
    @3
    cR
    cgrp
    wcel
    #
    @6
    cR
    cbs
    cfv
    #
    wcel
    #
    @1
    @2
    @15
    @10
    wb
    @0
    @1
    @18
    @2
    cR
    ringgrp
    3ad2ant1
    @0
    @1
    @20
    @2
    @19
    cR
    @6
    @19
    eqid
    #
    @17
    ringidcl
    3ad2ant1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @6
    @7
    cR
    cM
    cN
    @13
    @19
    c.0
    @21
    @16
    @7
    eqid
    #
    chrid.z
    odcong
    syl112anc
    syl5bbr
    @3
    @11
    @8
    @12
    @9
    @0
    @1
    @11
    @8
    wceq
    @2
    cR
    @7
    @6
    cL
    cM
    chrid.l
    @22
    @17
    zrhmulg
    3adant3
    @0
    @2
    @12
    @9
    wceq
    @1
    cR
    @7
    @6
    cL
    cN
    chrid.l
    @22
    @17
    zrhmulg
    3adant2
    eqeq12d
    bitr4d
end
