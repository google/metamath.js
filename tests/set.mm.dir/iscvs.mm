include "ccvs.mm"
include "wcel.mm"
include "cclm.mm"
include "clvec.mm"
include "wa.mm"
include "csca.mm"
include "cfv.mm"
include "cdr.mm"
include "df-cvs.mm"
include "elin2.mm"
include "clmod.mm"
include "clmlmod.mm"
include "wb.mm"
include "eqid.mm"
include "islvec.mm"
include "a1i.mm"
include "mpbirand.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem iscvs
  let cW: class W


  assert |- ( W e. CVec <-> ( W e. CMod /\ ( Scalar ` W ) e. DivRing ) )

  proof
    cW
    ccvs
    wcel
    cW
    cclm
    wcel
    #
    cW
    clvec
    wcel
    #
    wa
    @0
    cW
    csca
    cfv
    #
    cdr
    wcel
    #
    wa
    cW
    cclm
    clvec
    ccvs
    df-cvs
    elin2
    @0
    @1
    @3
    @0
    @1
    cW
    clmod
    wcel
    #
    @3
    cW
    clmlmod
    @1
    @4
    @3
    wa
    wb
    @0
    @2
    cW
    @2
    eqid
    islvec
    a1i
    mpbirand
    pm5.32i
    bitri
end
