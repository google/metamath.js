include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cfv.mm"
include "cn0.mm"
include "deg1nn0cl.mm"
include "3expia.mm"
include "wn.mm"
include "wceq.mm"
include "cmnf.mm"
include "cr.mm"
include "mnfnre.mm"
include "neli.mm"
include "nn0re.mm"
include "mto.mm"
include "deg1z.mm"
include "adantr.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "fveq2.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "necon2ad.mm"
include "impbid.mm"

theorem deg1nn0clb
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


  assert |- ( ( R e. Ring /\ F e. B ) -> ( F =/= .0. <-> ( D ` F ) e. NN0 ) )

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
    c.0
    wne
    #
    cF
    cD
    cfv
    #
    cn0
    wcel
    #
    @0
    @1
    @3
    @5
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
    3expia
    @2
    @5
    cF
    c.0
    @2
    @5
    wn
    cF
    c.0
    wceq
    #
    c.0
    cD
    cfv
    #
    cn0
    wcel
    #
    wn
    @2
    @8
    cmnf
    cn0
    wcel
    #
    @9
    cmnf
    cr
    wcel
    cmnf
    cr
    mnfnre
    neli
    cmnf
    nn0re
    mto
    @2
    @7
    cmnf
    cn0
    @0
    @7
    cmnf
    wceq
    @1
    cD
    cP
    cR
    c.0
    deg1z.d
    deg1z.p
    deg1z.z
    deg1z
    adantr
    eleq1d
    mtbiri
    @6
    @5
    @8
    @6
    @4
    @7
    cn0
    cF
    c.0
    cD
    fveq2
    eleq1d
    notbid
    syl5ibrcom
    necon2ad
    impbid
end
