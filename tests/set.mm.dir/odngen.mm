include "cgrp.mm"
include "wcel.mm"
include "cfv.mm"
include "cn.mm"
include "w3a.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "cmg.mm"
include "cmpt.mm"
include "ccnv.mm"
include "wceq.mm"
include "csn.mm"
include "crab.mm"
include "cima.mm"
include "chash.mm"
include "cphi.mm"
include "eqid.mm"
include "mptpreima.mm"
include "fveq2i.mm"
include "wf1.mm"
include "wss.mm"
include "wf1o.mm"
include "odf1o2.mm"
include "f1ocnv.mm"
include "f1of1.mm"
include "3syl.mm"
include "ssrab2.mm"
include "wa.mm"
include "cen.mm"
include "wbr.mm"
include "fvex.mm"
include "rabex.mm"
include "f1imaen.mm"
include "hasheni.mm"
include "syl.mm"
include "sylancl.mm"
include "cgcd.mm"
include "c1.mm"
include "wb.mm"
include "cz.mm"
include "simpl1.mm"
include "simpl2.mm"
include "elfzoelz.mm"
include "adantl.mm"
include "cycsubg2cl.mm"
include "syl3anc.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab3.mm"
include "simpl3.mm"
include "odmulgeq.mm"
include "syl31anc.mm"
include "bitrd.mm"
include "rabbidva.mm"
include "fveq2d.mm"
include "dfphi2.mm"
include "3ad2ant3.mm"
include "eqtr4d.mm"
include "3eqtr3a.mm"

theorem odngen
  let vx: setvar x
  let cA: class A
  let cG: class G
  let cK: class K
  let cO: class O
  let cX: class X
  let vy: setvar y
  assume odhash.x: |- X = ( Base ` G )
  assume odhash.o: |- O = ( od ` G )
  assume odhash.k: |- K = ( mrCls ` ( SubGrp ` G ) )

  disjoint A x
  disjoint G x
  disjoint K x
  disjoint O x
  disjoint X x
  disjoint x y
  disjoint A y
  disjoint G y
  disjoint K y
  disjoint O y
  disjoint X y
  assert |- ( ( G e. Grp /\ A e. X /\ ( O ` A ) e. NN ) -> ( # ` { x e. ( K ` { A } ) | ( O ` x ) = ( O ` A ) } ) = ( phi ` ( O ` A ) ) )

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
    vy
    cc0
    @2
    cfzo
    co
    #
    vy
    cv
    #
    cA
    cG
    cmg
    cfv
    #
    co
    #
    cmpt
    #
    ccnv
    #
    vx
    cv
    #
    cO
    cfv
    #
    @2
    wceq
    #
    vx
    cA
    csn
    #
    cK
    cfv
    #
    crab
    #
    cima
    #
    chash
    cfv
    #
    @8
    @16
    wcel
    #
    vy
    @5
    crab
    #
    chash
    cfv
    #
    @16
    chash
    cfv
    #
    @2
    cphi
    cfv
    #
    @17
    @20
    chash
    vy
    @5
    @8
    @16
    @9
    @9
    eqid
    mptpreima
    fveq2i
    @4
    @15
    @5
    @10
    wf1
    #
    @16
    @15
    wss
    #
    @18
    @22
    wceq
    #
    @4
    @5
    @15
    @9
    wf1o
    @15
    @5
    @10
    wf1o
    @24
    vy
    cA
    @7
    cG
    cK
    cO
    cX
    odhash.x
    @7
    eqid
    #
    odhash.o
    odhash.k
    odf1o2
    @5
    @15
    @9
    f1ocnv
    @15
    @5
    @10
    f1of1
    3syl
    @13
    vx
    @15
    ssrab2
    @24
    @25
    wa
    @17
    @16
    cen
    wbr
    @26
    @15
    @5
    @16
    @10
    @13
    vx
    @15
    @14
    cK
    fvex
    rabex
    f1imaen
    @17
    @16
    hasheni
    syl
    sylancl
    @4
    @21
    @6
    @2
    cgcd
    co
    c1
    wceq
    #
    vy
    @5
    crab
    #
    chash
    cfv
    #
    @23
    @4
    @20
    @29
    chash
    @4
    @19
    @28
    vy
    @5
    @4
    @6
    @5
    wcel
    #
    wa
    #
    @19
    @8
    cO
    cfv
    #
    @2
    wceq
    #
    @28
    @32
    @8
    @15
    wcel
    #
    @19
    @34
    wb
    @32
    @0
    @1
    @6
    cz
    wcel
    #
    @35
    @0
    @1
    @3
    @31
    simpl1
    #
    @0
    @1
    @3
    @31
    simpl2
    #
    @31
    @36
    @4
    @6
    cc0
    @2
    elfzoelz
    adantl
    #
    cA
    @7
    cG
    cK
    @6
    cX
    odhash.x
    @27
    odhash.k
    cycsubg2cl
    syl3anc
    @13
    @34
    vx
    @8
    @15
    @11
    @8
    wceq
    @12
    @33
    @2
    @11
    @8
    cO
    fveq2
    eqeq1d
    elrab3
    syl
    @32
    @0
    @1
    @36
    @3
    @34
    @28
    wb
    @37
    @38
    @39
    @0
    @1
    @3
    @31
    simpl3
    cA
    @7
    cG
    @6
    cO
    cX
    odhash.x
    odhash.o
    @27
    odmulgeq
    syl31anc
    bitrd
    rabbidva
    fveq2d
    @3
    @0
    @23
    @30
    wceq
    @1
    vy
    @2
    dfphi2
    3ad2ant3
    eqtr4d
    3eqtr3a
end
