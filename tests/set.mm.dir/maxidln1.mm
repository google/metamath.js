include "crngo.mm"
include "wcel.mm"
include "cmaxidl.mm"
include "cfv.mm"
include "wa.mm"
include "wn.mm"
include "c1st.mm"
include "crn.mm"
include "wne.mm"
include "eqid.mm"
include "maxidlnr.mm"
include "cidl.mm"
include "wb.mm"
include "maxidlidl.mm"
include "1idl.mm"
include "necon3bbid.mm"
include "syldan.mm"
include "mpbird.mm"

theorem maxidln1
  let cR: class R
  let cU: class U
  let cH: class H
  let cM: class M
  assume maxidln1.1: |- H = ( 2nd ` R )
  assume maxidln1.2: |- U = ( GId ` H )


  assert |- ( ( R e. RingOps /\ M e. ( MaxIdl ` R ) ) -> -. U e. M )

  proof
    cR
    crngo
    wcel
    #
    cM
    cR
    cmaxidl
    cfv
    wcel
    #
    wa
    cU
    cM
    wcel
    #
    wn
    #
    cM
    cR
    c1st
    cfv
    #
    crn
    #
    wne
    #
    cR
    @4
    cM
    @5
    @4
    eqid
    #
    @5
    eqid
    #
    maxidlnr
    @0
    @1
    cM
    cR
    cidl
    cfv
    wcel
    #
    @3
    @6
    wb
    cR
    cM
    maxidlidl
    @0
    @9
    wa
    @2
    cM
    @5
    cR
    cU
    @4
    cH
    cM
    @5
    @7
    maxidln1.1
    @8
    maxidln1.2
    1idl
    necon3bbid
    syldan
    mpbird
end
