include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "pmapat.mm"
include "eleq2d.mm"
include "wb.mm"
include "elsn2g.mm"
include "adantl.mm"
include "bitrd.mm"

theorem elpmapat
  let cA: class A
  let cP: class P
  let cK: class K
  let cM: class M
  let cX: class X
  let vq: setvar q
  assume pmapat.a: |- A = ( Atoms ` K )
  assume pmapat.m: |- M = ( pmap ` K )


  assert |- ( ( K e. HL /\ P e. A ) -> ( X e. ( M ` P ) <-> X = P ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    wa
    #
    cX
    cP
    cM
    cfv
    #
    wcel
    cX
    cP
    csn
    #
    wcel
    #
    cX
    cP
    wceq
    #
    @2
    @3
    @4
    cX
    cA
    cP
    cK
    cM
    pmapat.a
    pmapat.m
    pmapat
    eleq2d
    @1
    @5
    @6
    wb
    @0
    cX
    cP
    cA
    elsn2g
    adantl
    bitrd
end
