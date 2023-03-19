include "cgrp.mm"
include "wcel.mm"
include "cfv.mm"
include "cn.mm"
include "w3a.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "csn.mm"
include "cv.mm"
include "cmpt.mm"
include "wfo.mm"
include "ccnv.mm"
include "wfun.mm"
include "wf1o.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "wf1.mm"
include "wa.mm"
include "cz.mm"
include "simpl1.mm"
include "elfzoelz.mm"
include "adantl.mm"
include "simpl2.mm"
include "mulgcl.mm"
include "syl3anc.mm"
include "ex.mm"
include "wb.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "simpl3.mm"
include "nncnd.mm"
include "subid1d.mm"
include "breq1d.mm"
include "fzocongeq.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "c0g.mm"
include "eqid.mm"
include "odcong.mm"
include "syl112anc.mm"
include "3bitr3rd.mm"
include "dom2lem.mm"
include "f1fn.mm"
include "syl.mm"
include "wss.mm"
include "cres.mm"
include "resss.mm"
include "ssriv.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "oveq1.mm"
include "cbvmptv.mm"
include "3sstr3i.mm"
include "rnss.mm"
include "mp1i.mm"
include "wf.mm"
include "wrex.mm"
include "cmo.mm"
include "simpr.mm"
include "zmodfzo.mm"
include "syl2anc.mm"
include "odmod.mm"
include "3an1rs.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "cvv.mm"
include "ovex.mm"
include "elrnmpt.mm"
include "sylibr.mm"
include "fmptd.mm"
include "frn.mm"
include "eqssd.mm"
include "cycsubg2.mm"
include "3adant3.mm"
include "eqtr4d.mm"
include "df-fo.mm"
include "sylanbrc.mm"
include "df-f1.mm"
include "simprbi.mm"
include "dff1o3.mm"

theorem odf1o2
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
  assert |- ( ( G e. Grp /\ A e. X /\ ( O ` A ) e. NN ) -> ( x e. ( 0 ..^ ( O ` A ) ) |-> ( x .x. A ) ) : ( 0 ..^ ( O ` A ) ) -1-1-onto-> ( K ` { A } ) )

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
    cn
    wcel
    #
    w3a
    #
    cc0
    @2
    cfzo
    co
    #
    cA
    csn
    cK
    cfv
    #
    vx
    @5
    vx
    cv
    #
    cA
    c.x
    co
    #
    cmpt
    #
    wfo
    #
    @9
    ccnv
    wfun
    #
    @5
    @6
    @9
    wf1o
    @4
    @9
    @5
    wfn
    #
    @9
    crn
    #
    @6
    wceq
    @10
    @4
    @5
    cX
    @9
    wf1
    #
    @12
    @4
    vx
    vy
    @5
    cX
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
    @5
    wcel
    #
    @8
    cX
    wcel
    #
    @4
    @17
    wa
    @0
    @7
    cz
    wcel
    #
    @1
    @18
    @0
    @1
    @3
    @17
    simpl1
    @17
    @19
    @4
    @7
    cc0
    @2
    elfzoelz
    #
    adantl
    @0
    @1
    @3
    @17
    simpl2
    cX
    c.x
    cG
    @7
    cA
    odf1o1.x
    odf1o1.t
    mulgcl
    syl3anc
    ex
    @4
    @17
    @15
    @5
    wcel
    #
    wa
    #
    @8
    @16
    wceq
    #
    @7
    @15
    wceq
    #
    wb
    @4
    @22
    wa
    #
    @2
    cc0
    cmin
    co
    #
    @7
    @15
    cmin
    co
    #
    cdvds
    wbr
    #
    @2
    @27
    cdvds
    wbr
    #
    @24
    @23
    @25
    @26
    @2
    @27
    cdvds
    @25
    @2
    @25
    @2
    @0
    @1
    @3
    @22
    simpl3
    nncnd
    subid1d
    breq1d
    @22
    @28
    @24
    wb
    @4
    @7
    @15
    cc0
    @2
    fzocongeq
    adantl
    @25
    @0
    @1
    @19
    @15
    cz
    wcel
    #
    @29
    @23
    wb
    @0
    @1
    @3
    @22
    simpl1
    @0
    @1
    @3
    @22
    simpl2
    @17
    @19
    @4
    @21
    @20
    ad2antrl
    @21
    @30
    @4
    @17
    @15
    cc0
    @2
    elfzoelz
    ad2antll
    cA
    c.x
    cG
    @7
    @15
    cO
    cX
    cG
    c0g
    cfv
    #
    odf1o1.x
    odf1o1.o
    odf1o1.t
    @31
    eqid
    #
    odcong
    syl112anc
    3bitr3rd
    ex
    dom2lem
    #
    @5
    cX
    @9
    f1fn
    syl
    @4
    @13
    vy
    cz
    @16
    cmpt
    #
    crn
    #
    @6
    @4
    @13
    @35
    @9
    @34
    wss
    @13
    @35
    wss
    @4
    vx
    cz
    @8
    cmpt
    #
    @5
    cres
    #
    @36
    @9
    @34
    @36
    @5
    resss
    @5
    cz
    wss
    @37
    @9
    wceq
    vx
    @5
    cz
    @20
    ssriv
    vx
    cz
    @5
    @8
    resmpt
    ax-mp
    vx
    vy
    cz
    @8
    @16
    @7
    @15
    cA
    c.x
    oveq1
    cbvmptv
    3sstr3i
    @9
    @34
    rnss
    mp1i
    @4
    cz
    @13
    @34
    wf
    @35
    @13
    wss
    @4
    vy
    cz
    @16
    @13
    @34
    @4
    @30
    wa
    #
    @16
    @8
    wceq
    #
    vx
    @5
    wrex
    #
    @16
    @13
    wcel
    #
    @38
    @15
    @2
    cmo
    co
    #
    @5
    wcel
    #
    @16
    @42
    cA
    c.x
    co
    #
    wceq
    #
    @40
    @38
    @30
    @3
    @43
    @4
    @30
    simpr
    @0
    @1
    @3
    @30
    simpl3
    @15
    @2
    zmodfzo
    syl2anc
    @38
    @44
    @16
    @0
    @1
    @30
    @3
    @44
    @16
    wceq
    cA
    c.x
    cG
    @15
    cO
    cX
    @31
    odf1o1.x
    odf1o1.o
    odf1o1.t
    @32
    odmod
    3an1rs
    eqcomd
    @39
    @45
    vx
    @42
    @5
    @7
    @42
    wceq
    @8
    @44
    @16
    @7
    @42
    cA
    c.x
    oveq1
    eqeq2d
    rspcev
    syl2anc
    @16
    cvv
    wcel
    @41
    @40
    wb
    @15
    cA
    c.x
    ovex
    vx
    @5
    @8
    @16
    @9
    cvv
    @9
    eqid
    elrnmpt
    ax-mp
    sylibr
    @34
    eqid
    #
    fmptd
    cz
    @13
    @34
    frn
    syl
    eqssd
    @0
    @1
    @6
    @35
    wceq
    @3
    vy
    cA
    c.x
    @34
    cG
    cK
    cX
    odf1o1.x
    odf1o1.t
    @46
    odf1o1.k
    cycsubg2
    3adant3
    eqtr4d
    @5
    @6
    @9
    df-fo
    sylanbrc
    @4
    @14
    @11
    @33
    @14
    @5
    cX
    @9
    wf
    @11
    @5
    cX
    @9
    df-f1
    simprbi
    syl
    @5
    @6
    @9
    dff1o3
    sylanbrc
end
