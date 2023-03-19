include "cnzr.mm"
include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "wa.mm"
include "crg.mm"
include "cur.mm"
include "c0g.mm"
include "wne.mm"
include "subrgring.mm"
include "adantl.mm"
include "eqid.mm"
include "nzrnz.mm"
include "adantr.mm"
include "wceq.mm"
include "subrg1.mm"
include "subrg0.mm"
include "3netr3d.mm"
include "isnzr.mm"
include "sylanbrc.mm"

theorem subrgnzr
  let cA: class A
  let cR: class R
  let cS: class S
  assume subrgnzr.1: |- S = ( R |`s A )


  assert |- ( ( R e. NzRing /\ A e. ( SubRing ` R ) ) -> S e. NzRing )

  proof
    cR
    cnzr
    wcel
    #
    cA
    cR
    csubrg
    cfv
    wcel
    #
    wa
    #
    cS
    crg
    wcel
    #
    cS
    cur
    cfv
    #
    cS
    c0g
    cfv
    #
    wne
    cS
    cnzr
    wcel
    @1
    @3
    @0
    cA
    cR
    cS
    subrgnzr.1
    subrgring
    adantl
    @2
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    @4
    @5
    @0
    @6
    @7
    wne
    @1
    cR
    @6
    @7
    @6
    eqid
    #
    @7
    eqid
    #
    nzrnz
    adantr
    @1
    @6
    @4
    wceq
    @0
    cA
    cR
    cS
    @6
    subrgnzr.1
    @8
    subrg1
    adantl
    @1
    @7
    @5
    wceq
    @0
    cA
    cR
    cS
    @7
    subrgnzr.1
    @9
    subrg0
    adantl
    3netr3d
    cS
    @4
    @5
    @4
    eqid
    @5
    eqid
    isnzr
    sylanbrc
end
