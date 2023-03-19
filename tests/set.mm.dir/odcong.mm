include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "wceq.mm"
include "csg.mm"
include "wb.mm"
include "zsubcl.mm"
include "oddvds.mm"
include "syl3an3.mm"
include "simp1.mm"
include "simp3l.mm"
include "simp3r.mm"
include "simp2.mm"
include "eqid.mm"
include "mulgsubdir.mm"
include "syl13anc.mm"
include "eqeq1d.mm"
include "mulgcl.mm"
include "syl3anc.mm"
include "grpsubeq0.mm"
include "3bitrd.mm"

theorem odcong
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cM: class M
  let cN: class N
  let cO: class O
  let cX: class X
  let c.0: class .0.
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  assume odcl.1: |- X = ( Base ` G )
  assume odcl.2: |- O = ( od ` G )
  assume odid.3: |- .x. = ( .g ` G )
  assume odid.4: |- .0. = ( 0g ` G )


  assert |- ( ( G e. Grp /\ A e. X /\ ( M e. ZZ /\ N e. ZZ ) ) -> ( ( O ` A ) || ( M - N ) <-> ( M .x. A ) = ( N .x. A ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
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
    wa
    #
    w3a
    #
    cA
    cO
    cfv
    cM
    cN
    cmin
    co
    #
    cdvds
    wbr
    #
    @6
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    cM
    cA
    c.x
    co
    #
    cN
    cA
    c.x
    co
    #
    cG
    csg
    cfv
    #
    co
    #
    c.0
    wceq
    #
    @10
    @11
    wceq
    #
    @4
    @0
    @1
    @6
    cz
    wcel
    @7
    @9
    wb
    cM
    cN
    zsubcl
    cA
    c.x
    cG
    @6
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    oddvds
    syl3an3
    @5
    @8
    @13
    c.0
    @5
    @0
    @2
    @3
    @1
    @8
    @13
    wceq
    @0
    @1
    @4
    simp1
    #
    @0
    @1
    @2
    @3
    simp3l
    #
    @0
    @1
    @2
    @3
    simp3r
    #
    @0
    @1
    @4
    simp2
    #
    cX
    c.x
    cG
    cM
    @12
    cN
    cA
    odcl.1
    odid.3
    @12
    eqid
    #
    mulgsubdir
    syl13anc
    eqeq1d
    @5
    @0
    @10
    cX
    wcel
    #
    @11
    cX
    wcel
    #
    @14
    @15
    wb
    @16
    @5
    @0
    @2
    @1
    @21
    @16
    @17
    @19
    cX
    c.x
    cG
    cM
    cA
    odcl.1
    odid.3
    mulgcl
    syl3anc
    @5
    @0
    @3
    @1
    @22
    @16
    @18
    @19
    cX
    c.x
    cG
    cN
    cA
    odcl.1
    odid.3
    mulgcl
    syl3anc
    cX
    cG
    @12
    @10
    @11
    c.0
    odcl.1
    odid.4
    @20
    grpsubeq0
    syl3anc
    3bitrd
end
