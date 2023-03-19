include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "clmod.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "co.mm"
include "matlmod.mm"
include "adantr.mm"
include "matsca2.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "adantrd.mm"
include "imp.mm"
include "simprr.mm"
include "eqid.mm"
include "lmodvscl.mm"
include "syl3anc.mm"

theorem matvscl
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let c.x: class .x.
  let cK: class K
  let cN: class N
  let cX: class X
  assume matvscl.k: |- K = ( Base ` R )
  assume matvscl.a: |- A = ( N Mat R )
  assume matvscl.b: |- B = ( Base ` A )
  assume matvscl.s: |- .x. = ( .s ` A )


  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ ( C e. K /\ X e. B ) ) -> ( C .x. X ) e. B )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    #
    cC
    cK
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    wa
    cA
    clmod
    wcel
    #
    cC
    cA
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @2
    cC
    cX
    c.x
    co
    cB
    wcel
    @0
    @4
    @3
    cA
    cR
    cN
    matvscl.a
    matlmod
    adantr
    @0
    @3
    @7
    @0
    @1
    @7
    @2
    @0
    @1
    @7
    @0
    cK
    @6
    cC
    @0
    cK
    cR
    cbs
    cfv
    @6
    matvscl.k
    @0
    cR
    @5
    cbs
    cA
    cR
    cN
    crg
    matvscl.a
    matsca2
    fveq2d
    syl5eq
    eleq2d
    biimpd
    adantrd
    imp
    @0
    @1
    @2
    simprr
    cC
    c.x
    @5
    @6
    cB
    cA
    cX
    matvscl.b
    @5
    eqid
    matvscl.s
    @6
    eqid
    lmodvscl
    syl3anc
end
