include "crg.mm"
include "wcel.mm"
include "cui.mm"
include "cfv.mm"
include "cbs.mm"
include "c0g.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "wa.mm"
include "cdr.mm"
include "unitpropd.mm"
include "adantr.mm"
include "eqtr3d.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "adantlr.mm"
include "grpidpropd.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "eqeq12d.mm"
include "pm5.32da.mm"
include "ringpropd.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "eqid.mm"
include "isdrng.mm"
include "3bitr4g.mm"

theorem drngpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  assume drngpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume drngpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume drngpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume drngpropd.4: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( .r ` K ) y ) = ( x ( .r ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint L x
  disjoint L y
  assert |- ( ph -> ( K e. DivRing <-> L e. DivRing ) )

  proof
    wph
    cK
    crg
    wcel
    #
    cK
    cui
    cfv
    #
    cK
    cbs
    cfv
    #
    cK
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wceq
    #
    wa
    #
    cL
    crg
    wcel
    #
    cL
    cui
    cfv
    #
    cL
    cbs
    cfv
    #
    cL
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wceq
    #
    wa
    #
    cK
    cdr
    wcel
    cL
    cdr
    wcel
    wph
    @7
    @0
    @14
    wa
    @15
    wph
    @0
    @6
    @14
    wph
    @0
    wa
    #
    @1
    @9
    @5
    @13
    wph
    @1
    @9
    wceq
    @0
    wph
    vx
    vy
    cB
    cK
    cL
    drngpropd.1
    drngpropd.2
    drngpropd.4
    unitpropd
    adantr
    @16
    @2
    @10
    @4
    @12
    wph
    @2
    @10
    wceq
    @0
    wph
    cB
    @2
    @10
    drngpropd.1
    drngpropd.2
    eqtr3d
    adantr
    @16
    @3
    @11
    @16
    vx
    vy
    cB
    cK
    cL
    wph
    cB
    @2
    wceq
    @0
    drngpropd.1
    adantr
    wph
    cB
    @10
    wceq
    @0
    drngpropd.2
    adantr
    wph
    vx
    cv
    #
    cB
    wcel
    vy
    cv
    #
    cB
    wcel
    wa
    @17
    @18
    cK
    cplusg
    cfv
    co
    @17
    @18
    cL
    cplusg
    cfv
    co
    wceq
    @0
    drngpropd.3
    adantlr
    grpidpropd
    sneqd
    difeq12d
    eqeq12d
    pm5.32da
    wph
    @0
    @8
    @14
    wph
    vx
    vy
    cB
    cK
    cL
    drngpropd.1
    drngpropd.2
    drngpropd.3
    drngpropd.4
    ringpropd
    anbi1d
    bitrd
    @2
    cK
    @1
    @3
    @2
    eqid
    @1
    eqid
    @3
    eqid
    isdrng
    @10
    cL
    @9
    @11
    @10
    eqid
    @9
    eqid
    @11
    eqid
    isdrng
    3bitr4g
end
