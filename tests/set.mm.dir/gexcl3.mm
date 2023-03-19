include "cgrp.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "cfa.mm"
include "cn.mm"
include "cmg.mm"
include "c0g.mm"
include "wceq.mm"
include "simpl.mm"
include "cn0.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "grpbn0.mm"
include "r19.2z.mm"
include "sylan.mm"
include "cuz.mm"
include "elfzuz2.mm"
include "nnuz.mm"
include "syl6eleqr.mm"
include "rexlimivw.mm"
include "syl.mm"
include "nnnn0d.mm"
include "faccl.mm"
include "cdvds.mm"
include "wbr.mm"
include "elfzuzb.mm"
include "elnnuz.mm"
include "dvdsfac.mm"
include "sylanbr.mm"
include "sylbi.mm"
include "adantl.mm"
include "cz.mm"
include "wb.mm"
include "simpll.mm"
include "simplr.mm"
include "nnzd.mm"
include "eqid.mm"
include "oddvds.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "ex.mm"
include "ralimdva.mm"
include "imp.mm"
include "gexlem2.mm"
include "elfznn.mm"

theorem gexcl3
  let vx: setvar x
  let cE: class E
  let cG: class G
  let cN: class N
  let cO: class O
  let cX: class X
  assume gexod.1: |- X = ( Base ` G )
  assume gexod.2: |- E = ( gEx ` G )
  assume gexod.3: |- O = ( od ` G )

  disjoint E x
  disjoint G x
  disjoint N x
  disjoint X x
  assert |- ( ( G e. Grp /\ A. x e. X ( O ` x ) e. ( 1 ... N ) ) -> E e. NN )

  proof
    cG
    cgrp
    wcel
    #
    vx
    cv
    #
    cO
    cfv
    #
    c1
    cN
    cfz
    co
    wcel
    #
    vx
    cX
    wral
    #
    wa
    #
    cE
    c1
    cN
    cfa
    cfv
    #
    cfz
    co
    wcel
    #
    cE
    cn
    wcel
    @5
    @0
    @6
    cn
    wcel
    #
    @6
    @1
    cG
    cmg
    cfv
    #
    co
    cG
    c0g
    cfv
    #
    wceq
    #
    vx
    cX
    wral
    #
    @7
    @0
    @4
    simpl
    @5
    cN
    cn0
    wcel
    #
    @8
    @5
    cN
    @5
    @3
    vx
    cX
    wrex
    #
    cN
    cn
    wcel
    #
    @0
    cX
    c0
    wne
    @4
    @14
    cX
    cG
    gexod.1
    grpbn0
    @3
    vx
    cX
    r19.2z
    sylan
    @3
    @15
    vx
    cX
    @3
    cN
    c1
    cuz
    cfv
    #
    cn
    @2
    c1
    cN
    elfzuz2
    nnuz
    syl6eleqr
    #
    rexlimivw
    syl
    nnnn0d
    cN
    faccl
    #
    syl
    @0
    @4
    @12
    @0
    @3
    @11
    vx
    cX
    @0
    @1
    cX
    wcel
    #
    wa
    #
    @3
    @11
    @20
    @3
    wa
    #
    @2
    @6
    cdvds
    wbr
    #
    @11
    @3
    @22
    @20
    @3
    @2
    @16
    wcel
    #
    cN
    @2
    cuz
    cfv
    wcel
    #
    wa
    @22
    @2
    c1
    cN
    elfzuzb
    @23
    @2
    cn
    wcel
    @24
    @22
    @2
    elnnuz
    @2
    cN
    dvdsfac
    sylanbr
    sylbi
    adantl
    @21
    @0
    @19
    @6
    cz
    wcel
    @22
    @11
    wb
    @0
    @19
    @3
    simpll
    @0
    @19
    @3
    simplr
    @21
    @6
    @21
    @13
    @8
    @21
    cN
    @3
    @15
    @20
    @17
    adantl
    nnnn0d
    @18
    syl
    nnzd
    @1
    @9
    cG
    @6
    cO
    cX
    @10
    gexod.1
    gexod.3
    @9
    eqid
    #
    @10
    eqid
    #
    oddvds
    syl3anc
    mpbid
    ex
    ralimdva
    imp
    vx
    @9
    cE
    cG
    @6
    cgrp
    cX
    @10
    gexod.1
    gexod.2
    @25
    @26
    gexlem2
    syl3anc
    cE
    @6
    elfznn
    syl
end
