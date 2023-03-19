include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "simpl1.mm"
include "simpr.mm"
include "simpl3.mm"
include "simpl2.mm"
include "mulgass.mm"
include "syl13anc.mm"
include "eqeq1d.mm"
include "wb.mm"
include "zmulcld.mm"
include "eqid.mm"
include "oddvds.mm"
include "syl3anc.mm"
include "mulgcl.mm"
include "3bitr4rd.mm"

theorem odmulgid
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cK: class K
  let cN: class N
  let cO: class O
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume odmulgid.1: |- X = ( Base ` G )
  assume odmulgid.2: |- O = ( od ` G )
  assume odmulgid.3: |- .x. = ( .g ` G )


  assert |- ( ( ( G e. Grp /\ A e. X /\ N e. ZZ ) /\ K e. ZZ ) -> ( ( O ` ( N .x. A ) ) || K <-> ( O ` A ) || ( K x. N ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cK
    cz
    wcel
    #
    wa
    #
    cK
    cN
    cmul
    co
    #
    cA
    c.x
    co
    #
    cG
    c0g
    cfv
    #
    wceq
    #
    cK
    cN
    cA
    c.x
    co
    #
    c.x
    co
    #
    @8
    wceq
    #
    cA
    cO
    cfv
    @6
    cdvds
    wbr
    #
    @10
    cO
    cfv
    cK
    cdvds
    wbr
    #
    @5
    @7
    @11
    @8
    @5
    @0
    @4
    @2
    @1
    @7
    @11
    wceq
    @0
    @1
    @2
    @4
    simpl1
    #
    @3
    @4
    simpr
    #
    @0
    @1
    @2
    @4
    simpl3
    #
    @0
    @1
    @2
    @4
    simpl2
    #
    cX
    c.x
    cG
    cK
    cN
    cA
    odmulgid.1
    odmulgid.3
    mulgass
    syl13anc
    eqeq1d
    @5
    @0
    @1
    @6
    cz
    wcel
    @13
    @9
    wb
    @15
    @18
    @5
    cK
    cN
    @16
    @17
    zmulcld
    cA
    c.x
    cG
    @6
    cO
    cX
    @8
    odmulgid.1
    odmulgid.2
    odmulgid.3
    @8
    eqid
    #
    oddvds
    syl3anc
    @5
    @0
    @10
    cX
    wcel
    #
    @4
    @14
    @12
    wb
    @15
    @5
    @0
    @2
    @1
    @20
    @15
    @17
    @18
    cX
    c.x
    cG
    cN
    cA
    odmulgid.1
    odmulgid.3
    mulgcl
    syl3anc
    @16
    @10
    c.x
    cG
    cK
    cO
    cX
    @8
    odmulgid.1
    odmulgid.2
    odmulgid.3
    @19
    oddvds
    syl3anc
    3bitr4rd
end
