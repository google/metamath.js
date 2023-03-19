include "cal.mm"
include "wcel.mm"
include "w3a.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "atncmp.mm"
include "cbs.mm"
include "wb.mm"
include "atbase.mm"
include "atnle.mm"
include "syl3an3.mm"
include "bitr3d.mm"

theorem atnem0
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cK: class K
  let c.an: class ./\
  let c.0: class .0.
  assume atnem0.m: |- ./\ = ( meet ` K )
  assume atnem0.z: |- .0. = ( 0. ` K )
  assume atnem0.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. AtLat /\ P e. A /\ Q e. A ) -> ( P =/= Q <-> ( P ./\ Q ) = .0. ) )

  proof
    cK
    cal
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    w3a
    cP
    cQ
    cK
    cple
    cfv
    #
    wbr
    wn
    #
    cP
    cQ
    wne
    cP
    cQ
    c.an
    co
    c.0
    wceq
    #
    cA
    cP
    cQ
    cK
    @3
    @3
    eqid
    #
    atnem0.a
    atncmp
    @2
    @0
    @1
    cQ
    cK
    cbs
    cfv
    #
    wcel
    @4
    @5
    wb
    cA
    @7
    cQ
    cK
    @7
    eqid
    #
    atnem0.a
    atbase
    cA
    @7
    cP
    cK
    @3
    c.an
    cQ
    c.0
    @8
    @6
    atnem0.m
    atnem0.z
    atnem0.a
    atnle
    syl3an3
    bitr3d
end
