include "cgrp.mm"
include "wcel.mm"
include "cfn.mm"
include "w3a.mm"
include "cfv.mm"
include "cz.mm"
include "cv.mm"
include "cmg.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "chash.mm"
include "cdvds.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "eqid.mm"
include "dfod2.mm"
include "3adant2.mm"
include "wss.mm"
include "simp2.mm"
include "csubg.mm"
include "wa.mm"
include "cycsubgcl.mm"
include "simpld.mm"
include "subgss.mm"
include "syl.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "iftrued.mm"
include "eqtrd.mm"
include "wbr.mm"
include "lagsubg.mm"
include "eqbrtrd.mm"

theorem oddvds2
  let cA: class A
  let cG: class G
  let cO: class O
  let cX: class X
  let vx: setvar x
  assume odcl2.1: |- X = ( Base ` G )
  assume odcl2.2: |- O = ( od ` G )


  assert |- ( ( G e. Grp /\ X e. Fin /\ A e. X ) -> ( O ` A ) || ( # ` X ) )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cfn
    wcel
    #
    cA
    cX
    wcel
    #
    w3a
    #
    cA
    cO
    cfv
    #
    vx
    cz
    vx
    cv
    cA
    cG
    cmg
    cfv
    #
    co
    cmpt
    #
    crn
    #
    chash
    cfv
    #
    cX
    chash
    cfv
    #
    cdvds
    @3
    @4
    @7
    cfn
    wcel
    #
    @8
    cc0
    cif
    #
    @8
    @0
    @2
    @4
    @11
    wceq
    @1
    vx
    cA
    @5
    @6
    cG
    cO
    cX
    odcl2.1
    odcl2.2
    @5
    eqid
    #
    @6
    eqid
    #
    dfod2
    3adant2
    @3
    @10
    @8
    cc0
    @3
    @1
    @7
    cX
    wss
    #
    @10
    @0
    @1
    @2
    simp2
    #
    @3
    @7
    cG
    csubg
    cfv
    wcel
    #
    @14
    @3
    @16
    cA
    @7
    wcel
    #
    @0
    @2
    @16
    @17
    wa
    @1
    vx
    cA
    @5
    @6
    cG
    cX
    odcl2.1
    @12
    @13
    cycsubgcl
    3adant2
    simpld
    #
    cX
    @7
    cG
    odcl2.1
    subgss
    syl
    cX
    @7
    ssfi
    syl2anc
    iftrued
    eqtrd
    @3
    @16
    @1
    @8
    @9
    cdvds
    wbr
    @18
    @15
    cG
    cX
    @7
    odcl2.1
    lagsubg
    syl2anc
    eqbrtrd
end
