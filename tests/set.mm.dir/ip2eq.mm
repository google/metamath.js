include "cphl.mm"
include "wcel.mm"
include "w3a.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "oveq2.mm"
include "ralrimivw.mm"
include "csg.mm"
include "cfv.mm"
include "wi.mm"
include "clmod.mm"
include "phllmod.mm"
include "eqid.mm"
include "lmodvsubcl.mm"
include "syl3an1.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "syl.mm"
include "csca.mm"
include "c0g.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "ipsubdi.mm"
include "syl13anc.mm"
include "eqeq1d.mm"
include "wb.mm"
include "ipeq0.mm"
include "syl2anc.mm"
include "bitr3d.mm"
include "cgrp.mm"
include "cbs.mm"
include "3ad2ant1.mm"
include "lmodfgrp.mm"
include "ipcl.mm"
include "syl3anc.mm"
include "grpsubeq0.mm"
include "lmodgrp.mm"
include "3bitr3d.mm"
include "sylibd.mm"
include "impbid2.mm"

theorem ip2eq
  let vx: setvar x
  let cA: class A
  let cB: class B
  let c.xi: class .,
  let cV: class V
  let cW: class W
  assume ip2eq.h: |- ., = ( .i ` W )
  assume ip2eq.v: |- V = ( Base ` W )

  disjoint A x
  disjoint B x
  disjoint ., x
  disjoint V x
  disjoint W x
  assert |- ( ( W e. PreHil /\ A e. V /\ B e. V ) -> ( A = B <-> A. x e. V ( x ., A ) = ( x ., B ) ) )

  proof
    cW
    cphl
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    w3a
    #
    cA
    cB
    wceq
    #
    vx
    cv
    #
    cA
    c.xi
    co
    #
    @5
    cB
    c.xi
    co
    #
    wceq
    #
    vx
    cV
    wral
    #
    @4
    @8
    vx
    cV
    cA
    cB
    @5
    c.xi
    oveq2
    ralrimivw
    @3
    @9
    cA
    cB
    cW
    csg
    cfv
    #
    co
    #
    cA
    c.xi
    co
    #
    @11
    cB
    c.xi
    co
    #
    wceq
    #
    @4
    @3
    @11
    cV
    wcel
    #
    @9
    @14
    wi
    @0
    cW
    clmod
    wcel
    #
    @1
    @2
    @15
    cW
    phllmod
    #
    @10
    cV
    cW
    cA
    cB
    ip2eq.v
    @10
    eqid
    #
    lmodvsubcl
    syl3an1
    #
    @8
    @14
    vx
    @11
    cV
    @5
    @11
    wceq
    @6
    @12
    @7
    @13
    @5
    @11
    cA
    c.xi
    oveq1
    @5
    @11
    cB
    c.xi
    oveq1
    eqeq12d
    rspcv
    syl
    @3
    @12
    @13
    cW
    csca
    cfv
    #
    csg
    cfv
    #
    co
    #
    @20
    c0g
    cfv
    #
    wceq
    #
    @11
    cW
    c0g
    cfv
    #
    wceq
    #
    @14
    @4
    @3
    @11
    @11
    c.xi
    co
    #
    @23
    wceq
    #
    @24
    @26
    @3
    @27
    @22
    @23
    @3
    @0
    @15
    @1
    @2
    @27
    @22
    wceq
    @0
    @1
    @2
    simp1
    #
    @19
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp3
    #
    @11
    cA
    cB
    @21
    @20
    c.xi
    @10
    cV
    cW
    @20
    eqid
    #
    ip2eq.h
    ip2eq.v
    @18
    @21
    eqid
    #
    ipsubdi
    syl13anc
    eqeq1d
    @3
    @0
    @15
    @28
    @26
    wb
    @29
    @19
    @11
    @20
    c.xi
    cV
    cW
    @25
    @23
    @32
    ip2eq.h
    ip2eq.v
    @23
    eqid
    #
    @25
    eqid
    #
    ipeq0
    syl2anc
    bitr3d
    @3
    @20
    cgrp
    wcel
    #
    @12
    @20
    cbs
    cfv
    #
    wcel
    #
    @13
    @37
    wcel
    #
    @24
    @14
    wb
    @3
    @16
    @36
    @0
    @1
    @16
    @2
    @17
    3ad2ant1
    @20
    cW
    @32
    lmodfgrp
    syl
    @3
    @0
    @15
    @1
    @38
    @29
    @19
    @30
    @11
    cA
    @20
    c.xi
    @37
    cV
    cW
    @32
    ip2eq.h
    ip2eq.v
    @37
    eqid
    #
    ipcl
    syl3anc
    @3
    @0
    @15
    @2
    @39
    @29
    @19
    @31
    @11
    cB
    @20
    c.xi
    @37
    cV
    cW
    @32
    ip2eq.h
    ip2eq.v
    @40
    ipcl
    syl3anc
    @37
    @20
    @21
    @12
    @13
    @23
    @40
    @34
    @33
    grpsubeq0
    syl3anc
    @0
    cW
    cgrp
    wcel
    #
    @1
    @2
    @26
    @4
    wb
    @0
    @16
    @41
    @17
    cW
    lmodgrp
    syl
    cV
    cW
    @10
    cA
    cB
    @25
    ip2eq.v
    @35
    @18
    grpsubeq0
    syl3an1
    3bitr3d
    sylibd
    impbid2
end
