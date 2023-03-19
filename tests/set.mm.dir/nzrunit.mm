include "cnzr.mm"
include "wcel.mm"
include "wne.mm"
include "wn.mm"
include "wceq.mm"
include "cur.mm"
include "cfv.mm"
include "eqid.mm"
include "nzrnz.mm"
include "crg.mm"
include "wb.mm"
include "nzrring.mm"
include "0unit.mm"
include "necon3bbid.mm"
include "syl.mm"
include "mpbird.mm"
include "eleq1.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "necon2ad.mm"
include "imp.mm"

theorem nzrunit
  let cA: class A
  let cR: class R
  let cU: class U
  let c.0: class .0.
  assume nzrunit.1: |- U = ( Unit ` R )
  assume nzrunit.2: |- .0. = ( 0g ` R )


  assert |- ( ( R e. NzRing /\ A e. U ) -> A =/= .0. )

  proof
    cR
    cnzr
    wcel
    #
    cA
    cU
    wcel
    #
    cA
    c.0
    wne
    @0
    @1
    cA
    c.0
    @0
    @1
    wn
    cA
    c.0
    wceq
    #
    c.0
    cU
    wcel
    #
    wn
    #
    @0
    @4
    cR
    cur
    cfv
    #
    c.0
    wne
    #
    cR
    @5
    c.0
    @5
    eqid
    #
    nzrunit.2
    nzrnz
    @0
    cR
    crg
    wcel
    #
    @4
    @6
    wb
    cR
    nzrring
    @8
    @3
    @5
    c.0
    cR
    cU
    @5
    c.0
    nzrunit.1
    nzrunit.2
    @7
    0unit
    necon3bbid
    syl
    mpbird
    @2
    @1
    @3
    cA
    c.0
    cU
    eleq1
    notbid
    syl5ibrcom
    necon2ad
    imp
end
