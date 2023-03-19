include "wcel.mm"
include "wfun.mm"
include "wa.mm"
include "c0.mm"
include "wceq.mm"
include "ciedg.mm"
include "cfv.mm"
include "crn.mm"
include "cedg.mm"
include "edgvalOLD.mm"
include "syl5eq.mm"
include "adantr.mm"
include "eqeq1d.mm"
include "eqcomi.mm"
include "a1i.mm"
include "rneqd.mm"
include "wb.mm"
include "wrel.mm"
include "funrel.mm"
include "relrn0.mm"
include "bicomd.mm"
include "syl.mm"
include "adantl.mm"
include "3bitrd.mm"

theorem edg0iedg0OLD
  let cE: class E
  let cG: class G
  let cI: class I
  let cW: class W
  assume edg0iedg0.i: |- I = ( iEdg ` G )
  assume edg0iedg0.e: |- E = ( Edg ` G )


  assert |- ( ( G e. W /\ Fun I ) -> ( E = (/) <-> I = (/) ) )

  proof
    cG
    cW
    wcel
    #
    cI
    wfun
    #
    wa
    #
    cE
    c0
    wceq
    cG
    ciedg
    cfv
    #
    crn
    #
    c0
    wceq
    cI
    crn
    #
    c0
    wceq
    #
    cI
    c0
    wceq
    #
    @2
    cE
    @4
    c0
    @0
    cE
    @4
    wceq
    @1
    @0
    cE
    cG
    cedg
    cfv
    @4
    edg0iedg0.e
    cG
    cW
    edgvalOLD
    syl5eq
    adantr
    eqeq1d
    @2
    @4
    @5
    c0
    @2
    @3
    cI
    @3
    cI
    wceq
    @2
    cI
    @3
    edg0iedg0.i
    eqcomi
    a1i
    rneqd
    eqeq1d
    @1
    @6
    @7
    wb
    #
    @0
    @1
    cI
    wrel
    #
    @8
    cI
    funrel
    @9
    @7
    @6
    cI
    relrn0
    bicomd
    syl
    adantl
    3bitrd
end
