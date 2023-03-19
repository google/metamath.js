include "crg.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "csn.mm"
include "0ring.mm"
include "wi.mm"
include "ringidcl.mm"
include "eleq2.mm"
include "elsni.mm"
include "eqcomd.mm"
include "syl6bi.mm"
include "syl5com.mm"
include "adantr.mm"
include "mpd.mm"

theorem 0ring01eq
  let cB: class B
  let cR: class R
  let c.1: class .1.
  let c.0: class .0.
  assume 0ring.b: |- B = ( Base ` R )
  assume 0ring.0: |- .0. = ( 0g ` R )
  assume 0ring01eq.1: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ ( # ` B ) = 1 ) -> .0. = .1. )

  proof
    cR
    crg
    wcel
    #
    cB
    chash
    cfv
    c1
    wceq
    #
    wa
    cB
    c.0
    csn
    #
    wceq
    #
    c.0
    c.1
    wceq
    #
    cB
    cR
    c.0
    0ring.b
    0ring.0
    0ring
    @0
    @3
    @4
    wi
    @1
    @0
    c.1
    cB
    wcel
    #
    @3
    @4
    cB
    cR
    c.1
    0ring.b
    0ring01eq.1
    ringidcl
    @3
    @5
    c.1
    @2
    wcel
    #
    @4
    cB
    @2
    c.1
    eleq2
    @6
    c.1
    c.0
    c.1
    c.0
    elsni
    eqcomd
    syl6bi
    syl5com
    adantr
    mpd
end
