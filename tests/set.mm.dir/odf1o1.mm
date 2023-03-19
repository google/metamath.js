include "cgrp.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "w3a.mm"
include "cz.mm"
include "csn.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "wa.mm"
include "csubg.mm"
include "cmre.mm"
include "wss.mm"
include "cacs.mm"
include "simpl1.mm"
include "subgacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "simpl2.mm"
include "snssd.mm"
include "mrccl.mm"
include "syl2anc.mm"
include "simpr.mm"
include "mrcssidd.mm"
include "snidg.mm"
include "syl.mm"
include "sseldd.mm"
include "subgmulgcl.mm"
include "syl3anc.mm"
include "ex.mm"
include "wb.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "simpl3.mm"
include "breq1d.mm"
include "zsubcl.mm"
include "adantl.mm"
include "0dvds.mm"
include "bitrd.mm"
include "simprl.mm"
include "simprr.mm"
include "c0g.mm"
include "eqid.mm"
include "odcong.mm"
include "syl112anc.mm"
include "cc.mm"
include "zcn.mm"
include "subeq0.mm"
include "syl2an.mm"
include "3bitr3d.mm"
include "dom2lem.mm"
include "wf.mm"
include "crn.mm"
include "f1f.mm"
include "cycsubg2.mm"
include "3adant3.mm"
include "eqcomd.mm"
include "dffo2.mm"
include "sylanbrc.mm"
include "df-f1o.mm"

theorem odf1o1
  let vx: setvar x
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cK: class K
  let cO: class O
  let cX: class X
  let vy: setvar y
  assume odf1o1.x: |- X = ( Base ` G )
  assume odf1o1.t: |- .x. = ( .g ` G )
  assume odf1o1.o: |- O = ( od ` G )
  assume odf1o1.k: |- K = ( mrCls ` ( SubGrp ` G ) )

  disjoint A x
  disjoint G x
  disjoint K x
  disjoint O x
  disjoint .x. x
  disjoint X x
  disjoint x y
  disjoint A y
  disjoint G y
  disjoint K y
  disjoint O y
  disjoint .x. y
  disjoint X y
  assert |- ( ( G e. Grp /\ A e. X /\ ( O ` A ) = 0 ) -> ( x e. ZZ |-> ( x .x. A ) ) : ZZ -1-1-onto-> ( K ` { A } ) )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    cO
    cfv
    #
    cc0
    wceq
    #
    w3a
    #
    cz
    cA
    csn
    #
    cK
    cfv
    #
    vx
    cz
    vx
    cv
    #
    cA
    c.x
    co
    #
    cmpt
    #
    wf1
    #
    cz
    @6
    @9
    wfo
    #
    cz
    @6
    @9
    wf1o
    @4
    vx
    vy
    cz
    @6
    @8
    vy
    cv
    #
    cA
    c.x
    co
    #
    @4
    @7
    cz
    wcel
    #
    @8
    @6
    wcel
    #
    @4
    @14
    wa
    #
    @6
    cG
    csubg
    cfv
    #
    wcel
    #
    @14
    cA
    @6
    wcel
    @15
    @16
    @17
    cX
    cmre
    cfv
    wcel
    #
    @5
    cX
    wss
    @18
    @16
    @0
    @17
    cX
    cacs
    cfv
    wcel
    @19
    @0
    @1
    @3
    @14
    simpl1
    cX
    cG
    odf1o1.x
    subgacs
    @17
    cX
    acsmre
    3syl
    #
    @16
    cA
    cX
    @0
    @1
    @3
    @14
    simpl2
    #
    snssd
    #
    @17
    @5
    cK
    cX
    odf1o1.k
    mrccl
    syl2anc
    @4
    @14
    simpr
    @16
    @5
    @6
    cA
    @16
    @17
    @5
    cK
    cX
    @20
    odf1o1.k
    @22
    mrcssidd
    @16
    @1
    cA
    @5
    wcel
    @21
    cA
    cX
    snidg
    syl
    sseldd
    @6
    c.x
    cG
    @7
    cA
    odf1o1.t
    subgmulgcl
    syl3anc
    ex
    @4
    @14
    @12
    cz
    wcel
    #
    wa
    #
    @8
    @13
    wceq
    #
    @7
    @12
    wceq
    #
    wb
    @4
    @24
    wa
    #
    @2
    @7
    @12
    cmin
    co
    #
    cdvds
    wbr
    #
    @28
    cc0
    wceq
    #
    @25
    @26
    @27
    @29
    cc0
    @28
    cdvds
    wbr
    #
    @30
    @27
    @2
    cc0
    @28
    cdvds
    @0
    @1
    @3
    @24
    simpl3
    breq1d
    @27
    @28
    cz
    wcel
    #
    @31
    @30
    wb
    @24
    @32
    @4
    @7
    @12
    zsubcl
    adantl
    @28
    0dvds
    syl
    bitrd
    @27
    @0
    @1
    @14
    @23
    @29
    @25
    wb
    @0
    @1
    @3
    @24
    simpl1
    @0
    @1
    @3
    @24
    simpl2
    @4
    @14
    @23
    simprl
    @4
    @14
    @23
    simprr
    cA
    c.x
    cG
    @7
    @12
    cO
    cX
    cG
    c0g
    cfv
    #
    odf1o1.x
    odf1o1.o
    odf1o1.t
    @33
    eqid
    odcong
    syl112anc
    @24
    @30
    @26
    wb
    #
    @4
    @14
    @7
    cc
    wcel
    @12
    cc
    wcel
    @34
    @23
    @7
    zcn
    @12
    zcn
    @7
    @12
    subeq0
    syl2an
    adantl
    3bitr3d
    ex
    dom2lem
    #
    @4
    cz
    @6
    @9
    wf
    #
    @9
    crn
    #
    @6
    wceq
    @11
    @4
    @10
    @36
    @35
    cz
    @6
    @9
    f1f
    syl
    @4
    @6
    @37
    @0
    @1
    @6
    @37
    wceq
    @3
    vx
    cA
    c.x
    @9
    cG
    cK
    cX
    odf1o1.x
    odf1o1.t
    @9
    eqid
    odf1o1.k
    cycsubg2
    3adant3
    eqcomd
    cz
    @6
    @9
    dffo2
    sylanbrc
    cz
    @6
    @9
    df-f1o
    sylanbrc
end
