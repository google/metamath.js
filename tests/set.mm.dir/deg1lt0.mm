include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wne.mm"
include "wn.mm"
include "w3a.mm"
include "cn0.mm"
include "deg1nn0cl.mm"
include "nn0nlt0.mm"
include "syl.mm"
include "3expia.mm"
include "necon4ad.mm"
include "cmnf.mm"
include "deg1z.mm"
include "mnflt0.mm"
include "syl6eqbr.mm"
include "adantr.mm"
include "fveq2.mm"
include "breq1d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem deg1lt0
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  let c.0: class .0.
  assume deg1z.d: |- D = ( deg1 ` R )
  assume deg1z.p: |- P = ( Poly1 ` R )
  assume deg1z.z: |- .0. = ( 0g ` P )
  assume deg1nn0cl.b: |- B = ( Base ` P )


  assert |- ( ( R e. Ring /\ F e. B ) -> ( ( D ` F ) < 0 <-> F = .0. ) )

  proof
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    wa
    #
    cF
    cD
    cfv
    #
    cc0
    clt
    wbr
    #
    cF
    c.0
    wceq
    #
    @2
    @4
    cF
    c.0
    @0
    @1
    cF
    c.0
    wne
    #
    @4
    wn
    #
    @0
    @1
    @6
    w3a
    @3
    cn0
    wcel
    @7
    cB
    cD
    cP
    cR
    cF
    c.0
    deg1z.d
    deg1z.p
    deg1z.z
    deg1nn0cl.b
    deg1nn0cl
    @3
    nn0nlt0
    syl
    3expia
    necon4ad
    @2
    @4
    @5
    c.0
    cD
    cfv
    #
    cc0
    clt
    wbr
    #
    @0
    @9
    @1
    @0
    @8
    cmnf
    cc0
    clt
    cD
    cP
    cR
    c.0
    deg1z.d
    deg1z.p
    deg1z.z
    deg1z
    mnflt0
    syl6eqbr
    adantr
    @5
    @3
    @8
    cc0
    clt
    cF
    c.0
    cD
    fveq2
    breq1d
    syl5ibrcom
    impbid
end
