include "wcel.mm"
include "wa.mm"
include "crs.mm"
include "co.mm"
include "crh.mm"
include "ccnv.mm"
include "wf1o.mm"
include "isrim0.mm"
include "wb.mm"
include "wi.mm"
include "rhmf1o.mm"
include "bicomd.mm"
include "a1i.mm"
include "pm5.32d.mm"
include "bitrd.mm"

theorem isrim
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let cV: class V
  let cW: class W
  assume rhmf1o.b: |- B = ( Base ` R )
  assume rhmf1o.c: |- C = ( Base ` S )


  assert |- ( ( R e. V /\ S e. W ) -> ( F e. ( R RingIso S ) <-> ( F e. ( R RingHom S ) /\ F : B -1-1-onto-> C ) ) )

  proof
    cR
    cV
    wcel
    cS
    cW
    wcel
    wa
    #
    cF
    cR
    cS
    crs
    co
    wcel
    cF
    cR
    cS
    crh
    co
    wcel
    #
    cF
    ccnv
    cS
    cR
    crh
    co
    wcel
    #
    wa
    @1
    cB
    cC
    cF
    wf1o
    #
    wa
    cR
    cS
    cF
    cV
    cW
    isrim0
    @0
    @1
    @2
    @3
    @1
    @2
    @3
    wb
    wi
    @0
    @1
    @3
    @2
    cB
    cC
    cR
    cS
    cF
    rhmf1o.b
    rhmf1o.c
    rhmf1o
    bicomd
    a1i
    pm5.32d
    bitrd
end
