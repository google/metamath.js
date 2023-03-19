include "cdir.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "wex.mm"
include "cuni.mm"
include "cdm.mm"
include "dirdm.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "wral.mm"
include "cxp.mm"
include "ccnv.mm"
include "ccom.mm"
include "wss.mm"
include "wrel.mm"
include "cid.mm"
include "cres.mm"
include "eqid.mm"
include "isdir.mm"
include "ibi.mm"
include "simprrd.mm"
include "codir.mm"
include "sylib.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "anbi2d.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "sylbid.mm"
include "crn.mm"
include "reldir.mm"
include "relelrn.mm"
include "sylan.mm"
include "ex.mm"
include "cun.mm"
include "ssun2.mm"
include "dmrnssfld.mm"
include "sstri.mm"
include "syl5sseqr.mm"
include "sseld.mm"
include "syld.mm"
include "adantrd.mm"
include "ancrd.mm"
include "eximdv.mm"
include "df-rex.mm"
include "syl6ibr.mm"
include "3impib.mm"

theorem dirge
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  assume dirge.1: |- X = dom R

  disjoint A x
  disjoint B x
  disjoint R x
  disjoint X x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint R y
  disjoint R z
  disjoint X y
  disjoint X z
  assert |- ( ( R e. DirRel /\ A e. X /\ B e. X ) -> E. x e. X ( A R x /\ B R x ) )

  proof
    cR
    cdir
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    vx
    cv
    #
    cR
    wbr
    #
    cB
    @3
    cR
    wbr
    #
    wa
    #
    vx
    cX
    wrex
    #
    @0
    @1
    @2
    wa
    #
    @6
    vx
    wex
    #
    @7
    @0
    @8
    cA
    cR
    cuni
    cuni
    #
    wcel
    #
    cB
    @10
    wcel
    #
    wa
    #
    @9
    @0
    @1
    @11
    @2
    @12
    @0
    cX
    @10
    cA
    @0
    cX
    cR
    cdm
    #
    @10
    dirge.1
    cR
    dirdm
    syl5eq
    #
    eleq2d
    @0
    cX
    @10
    cB
    @15
    eleq2d
    anbi12d
    @0
    vy
    cv
    #
    @3
    cR
    wbr
    #
    vz
    cv
    #
    @3
    cR
    wbr
    #
    wa
    #
    vx
    wex
    #
    vz
    @10
    wral
    vy
    @10
    wral
    #
    @13
    @9
    @0
    @10
    @10
    cxp
    cR
    ccnv
    cR
    ccom
    wss
    #
    @22
    @0
    cR
    wrel
    #
    cid
    @10
    cres
    cR
    wss
    wa
    #
    cR
    cR
    ccom
    cR
    wss
    #
    @23
    @0
    @25
    @26
    @23
    wa
    wa
    @10
    cR
    cdir
    @10
    eqid
    isdir
    ibi
    simprrd
    vy
    vz
    vx
    @10
    @10
    cR
    codir
    sylib
    @21
    @9
    @4
    @19
    wa
    #
    vx
    wex
    vy
    vz
    cA
    cB
    @10
    @10
    @16
    cA
    wceq
    #
    @20
    @27
    vx
    @28
    @17
    @4
    @19
    @16
    cA
    @3
    cR
    breq1
    anbi1d
    exbidv
    @18
    cB
    wceq
    #
    @27
    @6
    vx
    @29
    @19
    @5
    @4
    @18
    cB
    @3
    cR
    breq1
    anbi2d
    exbidv
    rspc2v
    syl5com
    sylbid
    @0
    @9
    @3
    cX
    wcel
    #
    @6
    wa
    #
    vx
    wex
    @7
    @0
    @6
    @31
    vx
    @0
    @6
    @30
    @0
    @4
    @30
    @5
    @0
    @4
    @3
    cR
    crn
    #
    wcel
    #
    @30
    @0
    @4
    @33
    @0
    @24
    @4
    @33
    cR
    reldir
    cA
    @3
    cR
    relelrn
    sylan
    ex
    @0
    @32
    cX
    @3
    @0
    @10
    @32
    cX
    @32
    @14
    @32
    cun
    @10
    @32
    @14
    ssun2
    cR
    dmrnssfld
    sstri
    @15
    syl5sseqr
    sseld
    syld
    adantrd
    ancrd
    eximdv
    @6
    vx
    cX
    df-rex
    syl6ibr
    syld
    3impib
end
