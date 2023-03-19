include "crngo.mm"
include "wcel.mm"
include "c2nd.mm"
include "cfv.mm"
include "crn.mm"
include "cmagm.mm"
include "cexid.mm"
include "cin.mm"
include "wa.mm"
include "cmndo.mm"
include "rngomndo.mm"
include "eleq1i.mm"
include "mndoismgmOLD.mm"
include "mndoisexid.mm"
include "jca.mm"
include "sylbi.mm"
include "syl.mm"
include "elin.mm"
include "sylibr.mm"
include "eqid.mm"
include "cgi.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "iorlid.mm"
include "c1st.mm"
include "wceq.mm"
include "wb.mm"
include "rngorn1eq.mm"
include "eqtr.mm"
include "eleq2d.mm"
include "sylancr.mm"
include "mpbird.mm"

theorem rngo1cl
  let cR: class R
  let cU: class U
  let cH: class H
  let cX: class X
  assume ring1cl.1: |- X = ran ( 1st ` R )
  assume ring1cl.2: |- H = ( 2nd ` R )
  assume ring1cl.3: |- U = ( GId ` H )


  assert |- ( R e. RingOps -> U e. X )

  proof
    cR
    crngo
    wcel
    #
    cU
    cX
    wcel
    #
    cU
    cR
    c2nd
    cfv
    #
    crn
    #
    wcel
    #
    @0
    @2
    cmagm
    cexid
    cin
    wcel
    #
    @4
    @0
    @2
    cmagm
    wcel
    #
    @2
    cexid
    wcel
    #
    wa
    #
    @5
    @0
    cH
    cmndo
    wcel
    #
    @8
    cR
    cH
    ring1cl.2
    rngomndo
    @9
    @2
    cmndo
    wcel
    #
    @8
    cH
    @2
    cmndo
    ring1cl.2
    eleq1i
    @10
    @6
    @7
    @2
    mndoismgmOLD
    @2
    mndoisexid
    jca
    sylbi
    syl
    @2
    cmagm
    cexid
    elin
    sylibr
    cU
    @2
    @3
    @3
    eqid
    cU
    cH
    cgi
    cfv
    @2
    cgi
    cfv
    ring1cl.3
    cH
    @2
    cgi
    ring1cl.2
    fveq2i
    eqtri
    iorlid
    syl
    @0
    cX
    cR
    c1st
    cfv
    #
    crn
    #
    wceq
    #
    @12
    @3
    wceq
    #
    @1
    @4
    wb
    ring1cl.1
    cR
    @11
    @2
    @2
    eqid
    @11
    eqid
    rngorn1eq
    @13
    @14
    wa
    cX
    @3
    cU
    cX
    @12
    @3
    eqtr
    eleq2d
    sylancr
    mpbird
end
