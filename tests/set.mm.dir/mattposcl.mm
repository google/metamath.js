include "wcel.mm"
include "ctpos.mm"
include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "eqid.mm"
include "matbas2i.mm"
include "elmapi.mm"
include "tposf.mm"
include "3syl.mm"
include "cvv.mm"
include "cfn.mm"
include "wb.mm"
include "fvex.mm"
include "matrcl.mm"
include "simpld.mm"
include "xpfi.mm"
include "anidms.mm"
include "syl.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"
include "wa.mm"
include "wceq.mm"
include "matbas2.mm"
include "syl6eqr.mm"
include "eleqtrd.mm"

theorem mattposcl
  let cA: class A
  let cB: class B
  let cR: class R
  let cM: class M
  let cN: class N
  assume mattposcl.a: |- A = ( N Mat R )
  assume mattposcl.b: |- B = ( Base ` A )


  assert |- ( M e. B -> tpos M e. B )

  proof
    cM
    cB
    wcel
    #
    cM
    ctpos
    #
    cR
    cbs
    cfv
    #
    cN
    cN
    cxp
    #
    cmap
    co
    #
    cB
    @0
    @1
    @4
    wcel
    #
    @3
    @2
    @1
    wf
    #
    @0
    cM
    @4
    wcel
    @3
    @2
    cM
    wf
    @6
    cA
    cB
    cR
    @2
    cM
    cN
    mattposcl.a
    @2
    eqid
    #
    mattposcl.b
    matbas2i
    cM
    @2
    @3
    elmapi
    cN
    cN
    @2
    cM
    tposf
    3syl
    @0
    @2
    cvv
    wcel
    @3
    cfn
    wcel
    #
    @5
    @6
    wb
    cR
    cbs
    fvex
    @0
    cN
    cfn
    wcel
    #
    @8
    @0
    @9
    cR
    cvv
    wcel
    #
    cA
    cB
    cR
    cN
    cM
    mattposcl.a
    mattposcl.b
    matrcl
    #
    simpld
    @9
    @8
    cN
    cN
    xpfi
    anidms
    syl
    @2
    @3
    @1
    cvv
    cfn
    elmapg
    sylancr
    mpbird
    @0
    @4
    cA
    cbs
    cfv
    #
    cB
    @0
    @9
    @10
    wa
    @4
    @12
    wceq
    @11
    cA
    cR
    @2
    cN
    cvv
    mattposcl.a
    @7
    matbas2
    syl
    mattposcl.b
    syl6eqr
    eleqtrd
end
