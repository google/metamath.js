include "cdr.mm"
include "wcel.mm"
include "crg.mm"
include "clidl.mm"
include "cfv.mm"
include "clpidl.mm"
include "wss.mm"
include "clpir.mm"
include "drngring.mm"
include "ply1ring.mm"
include "syl.mm"
include "cv.mm"
include "wa.mm"
include "csn.mm"
include "crsp.mm"
include "wceq.mm"
include "cbs.mm"
include "wrex.mm"
include "cig1p.mm"
include "eqid.mm"
include "lidlss.mm"
include "adantl.mm"
include "ig1pcl.mm"
include "sseldd.mm"
include "ig1prsp.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "adantr.mm"
include "islpidl.mm"
include "mpbird.mm"
include "ex.mm"
include "ssrdv.mm"
include "islpir2.mm"
include "sylanbrc.mm"

theorem ply1lpir
  let cP: class P
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  assume ply1lpir.p: |- P = ( Poly1 ` R )


  assert |- ( R e. DivRing -> P e. LPIR )

  proof
    cR
    cdr
    wcel
    #
    cP
    crg
    wcel
    #
    cP
    clidl
    cfv
    #
    cP
    clpidl
    cfv
    #
    wss
    cP
    clpir
    wcel
    @0
    cR
    crg
    wcel
    @1
    cR
    drngring
    cP
    cR
    ply1lpir.p
    ply1ring
    syl
    #
    @0
    vi
    @2
    @3
    @0
    vi
    cv
    #
    @2
    wcel
    #
    @5
    @3
    wcel
    #
    @0
    @6
    wa
    #
    @7
    @5
    vj
    cv
    #
    csn
    #
    cP
    crsp
    cfv
    #
    cfv
    #
    wceq
    #
    vj
    cP
    cbs
    cfv
    #
    wrex
    #
    @8
    @5
    cR
    cig1p
    cfv
    #
    cfv
    #
    @14
    wcel
    @5
    @17
    csn
    #
    @11
    cfv
    #
    wceq
    #
    @15
    @8
    @5
    @14
    @17
    @6
    @5
    @14
    wss
    @0
    @14
    @5
    @2
    cP
    @14
    eqid
    #
    @2
    eqid
    #
    lidlss
    adantl
    cP
    cR
    @2
    @16
    @5
    ply1lpir.p
    @16
    eqid
    #
    @22
    ig1pcl
    sseldd
    cP
    cR
    @2
    @16
    @5
    @11
    ply1lpir.p
    @23
    @22
    @11
    eqid
    #
    ig1prsp
    @13
    @20
    vj
    @17
    @14
    @9
    @17
    wceq
    #
    @12
    @19
    @5
    @25
    @10
    @18
    @11
    @9
    @17
    sneq
    fveq2d
    eqeq2d
    rspcev
    syl2anc
    @8
    @1
    @7
    @15
    wb
    @0
    @1
    @6
    @4
    adantr
    @14
    @3
    cP
    vj
    @5
    @11
    @3
    eqid
    #
    @24
    @21
    islpidl
    syl
    mpbird
    ex
    ssrdv
    @3
    cP
    @2
    @26
    @22
    islpir2
    sylanbrc
end
