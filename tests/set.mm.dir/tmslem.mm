include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "wceq.mm"
include "cds.mm"
include "cmopn.mm"
include "ctopn.mm"
include "cdm.mm"
include "elfvdm.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "df-ds.mm"
include "1nn.mm"
include "2nn0.mm"
include "1nn0.mm"
include "1lt10.mm"
include "declti.mm"
include "2nn.mm"
include "decnncl.mm"
include "2strbas.mm"
include "syl.mm"
include "cxp.mm"
include "cres.mm"
include "cxr.mm"
include "wf.mm"
include "wfn.mm"
include "xmetf.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "2strop.mm"
include "reseq1d.mm"
include "eqtr3d.mm"
include "tmsval.mm"
include "setsmsbas.mm"
include "setsmsds.mm"
include "eqtrd.mm"
include "cvv.mm"
include "cnx.mm"
include "cop.mm"
include "cpr.mm"
include "prex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "setsmstopn.mm"
include "3jca.mm"

theorem tmslem
  let cD: class D
  let cK: class K
  let cM: class M
  let cX: class X
  let vd: setvar d
  assume tmsval.m: |- M = { <. ( Base ` ndx ) , X >. , <. ( dist ` ndx ) , D >. }
  assume tmsval.k: |- K = ( toMetSp ` D )


  assert |- ( D e. ( *Met ` X ) -> ( X = ( Base ` K ) /\ D = ( dist ` K ) /\ ( MetOpen ` D ) = ( TopOpen ` K ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    #
    wcel
    #
    cX
    cK
    cbs
    cfv
    wceq
    cD
    cK
    cds
    cfv
    #
    wceq
    cD
    cmopn
    cfv
    cK
    ctopn
    cfv
    wceq
    @1
    cD
    cK
    cM
    cX
    @1
    cX
    cxmt
    cdm
    #
    wcel
    cX
    cM
    cbs
    cfv
    wceq
    cD
    cX
    cxmt
    elfvdm
    cX
    cD
    cds
    cM
    c1
    c2
    cdc
    #
    @3
    tmsval.m
    df-ds
    c1
    c2
    c1
    1nn
    2nn0
    1nn0
    1lt10
    declti
    #
    c1
    c2
    1nn0
    2nn
    decnncl
    #
    2strbas
    syl
    #
    @1
    cD
    cX
    cX
    cxp
    #
    cres
    #
    cD
    cM
    cds
    cfv
    #
    @8
    cres
    @1
    @8
    cxr
    cD
    wf
    cD
    @8
    wfn
    @9
    cD
    wceq
    cD
    cX
    xmetf
    @8
    cxr
    cD
    ffn
    @8
    cD
    fnresdm
    3syl
    @1
    cD
    @10
    @8
    cX
    cD
    cds
    cM
    @4
    @0
    tmsval.m
    df-ds
    @5
    @6
    2strop
    #
    reseq1d
    eqtr3d
    #
    cD
    cK
    cM
    cX
    tmsval.m
    tmsval.k
    tmsval
    #
    setsmsbas
    @1
    cD
    @10
    @2
    @11
    @1
    cD
    cK
    cM
    cX
    @7
    @12
    @13
    setsmsds
    eqtrd
    @1
    cD
    cK
    cM
    cvv
    cX
    @7
    @12
    @13
    cM
    cvv
    wcel
    @1
    cM
    cnx
    cbs
    cfv
    cX
    cop
    #
    cnx
    cds
    cfv
    cD
    cop
    #
    cpr
    cvv
    tmsval.m
    @14
    @15
    prex
    eqeltri
    a1i
    setsmstopn
    3jca
end
