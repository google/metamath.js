include "crg.mm"
include "wcel.mm"
include "cfn.mm"
include "w3a.mm"
include "ccnv.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "csymg.mm"
include "eqid.mm"
include "psgninv.mm"
include "3adant1.mm"
include "fveq2d.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "c1.mm"
include "cneg.mm"
include "cpr.mm"
include "cress.mm"
include "co.mm"
include "cbs.mm"
include "wf.mm"
include "cghm.mm"
include "psgnghm2.mm"
include "ghmf.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "cminusg.mm"
include "symginv.mm"
include "3ad2ant3.mm"
include "cgrp.mm"
include "symggrp.mm"
include "simp3.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "fvco3.mm"
include "3eqtr4d.mm"

theorem zrhpsgninv
  let cP: class P
  let cR: class R
  let cS: class S
  let cF: class F
  let cN: class N
  let cY: class Y
  assume zrhpsgninv.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume zrhpsgninv.y: |- Y = ( ZRHom ` R )
  assume zrhpsgninv.s: |- S = ( pmSgn ` N )


  assert |- ( ( R e. Ring /\ N e. Fin /\ F e. P ) -> ( ( Y o. S ) ` `' F ) = ( ( Y o. S ) ` F ) )

  proof
    cR
    crg
    wcel
    #
    cN
    cfn
    wcel
    #
    cF
    cP
    wcel
    #
    w3a
    #
    cF
    ccnv
    #
    cS
    cfv
    #
    cY
    cfv
    #
    cF
    cS
    cfv
    #
    cY
    cfv
    #
    @4
    cY
    cS
    ccom
    #
    cfv
    #
    cF
    @9
    cfv
    #
    @3
    @5
    @7
    cY
    @1
    @2
    @5
    @7
    wceq
    @0
    cN
    cP
    cN
    csymg
    cfv
    #
    cF
    cS
    @12
    eqid
    #
    zrhpsgninv.s
    zrhpsgninv.p
    psgninv
    3adant1
    fveq2d
    @3
    cP
    ccnfld
    cmgp
    cfv
    c1
    c1
    cneg
    cpr
    cress
    co
    #
    cbs
    cfv
    #
    cS
    wf
    #
    @4
    cP
    wcel
    @10
    @6
    wceq
    @1
    @0
    @16
    @2
    @1
    cS
    @12
    @14
    cghm
    co
    wcel
    @16
    cN
    @12
    @14
    cS
    @13
    zrhpsgninv.s
    @14
    eqid
    psgnghm2
    @12
    @14
    cS
    cP
    @15
    zrhpsgninv.p
    @15
    eqid
    ghmf
    syl
    3ad2ant2
    #
    @3
    cF
    @12
    cminusg
    cfv
    #
    cfv
    #
    @4
    cP
    @2
    @0
    @19
    @4
    wceq
    @1
    cN
    cP
    cF
    @12
    @18
    @13
    zrhpsgninv.p
    @18
    eqid
    #
    symginv
    3ad2ant3
    @3
    @12
    cgrp
    wcel
    #
    @2
    @19
    cP
    wcel
    @1
    @0
    @21
    @2
    cN
    @12
    cfn
    @13
    symggrp
    3ad2ant2
    @0
    @1
    @2
    simp3
    #
    cP
    @12
    @18
    cF
    zrhpsgninv.p
    @20
    grpinvcl
    syl2anc
    eqeltrrd
    cP
    @15
    @4
    cY
    cS
    fvco3
    syl2anc
    @3
    @16
    @2
    @11
    @8
    wceq
    @17
    @22
    cP
    @15
    cF
    cY
    cS
    fvco3
    syl2anc
    3eqtr4d
end
