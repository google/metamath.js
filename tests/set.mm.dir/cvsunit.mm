include "ccvs.mm"
include "wcel.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "c0g.mm"
include "cfv.mm"
include "cui.mm"
include "cclm.mm"
include "wceq.mm"
include "id.mm"
include "cvsclm.mm"
include "clm0.mm"
include "syl.mm"
include "sneqd.mm"
include "difeq2d.mm"
include "clvec.mm"
include "cdr.mm"
include "cvslvec.mm"
include "lvecdrng.mm"
include "crg.mm"
include "eqid.mm"
include "isdrng.mm"
include "simprbi.mm"
include "3syl.mm"
include "eqtr4d.mm"

theorem cvsunit
  let cF: class F
  let cK: class K
  let cW: class W
  assume cvsdiv.f: |- F = ( Scalar ` W )
  assume cvsdiv.k: |- K = ( Base ` F )


  assert |- ( W e. CVec -> ( K \ { 0 } ) = ( Unit ` F ) )

  proof
    cW
    ccvs
    wcel
    #
    cK
    cc0
    csn
    #
    cdif
    cK
    cF
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    cF
    cui
    cfv
    #
    @0
    @1
    @3
    cK
    @0
    cc0
    @2
    @0
    cW
    cclm
    wcel
    cc0
    @2
    wceq
    @0
    cW
    @0
    id
    #
    cvsclm
    cF
    cW
    cvsdiv.f
    clm0
    syl
    sneqd
    difeq2d
    @0
    cW
    clvec
    wcel
    cF
    cdr
    wcel
    #
    @5
    @4
    wceq
    #
    @0
    cW
    @6
    cvslvec
    cF
    cW
    cvsdiv.f
    lvecdrng
    @7
    cF
    crg
    wcel
    @8
    cK
    cF
    @5
    @2
    cvsdiv.k
    @5
    eqid
    @2
    eqid
    isdrng
    simprbi
    3syl
    eqtr4d
end
