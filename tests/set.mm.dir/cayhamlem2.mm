include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "wa.mm"
include "cfv.mm"
include "cascl.mm"
include "csca.mm"
include "cbs.mm"
include "wceq.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "adantl.mm"
include "wb.mm"
include "matsca2.mm"
include "3adant3.mm"
include "fveq2d.mm"
include "syl5req.mm"
include "eleq2d.mm"
include "adantr.mm"
include "mpbird.mm"
include "eqid.mm"
include "asclval.mm"
include "syl.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "casa.mm"
include "matassa.mm"
include "cmgp.mm"
include "cmnd.mm"
include "crg.mm"
include "crngring.mm"
include "anim2i.mm"
include "matring.mm"
include "ringmgp.mm"
include "3syl.mm"
include "simprr.mm"
include "simpl3.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "asclmul2.mm"
include "eqtr2d.mm"

theorem cayhamlem2
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let c.ex: class .^
  let cH: class H
  let c.as: class .*
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  assume cayhamlem2.k: |- K = ( Base ` R )
  assume cayhamlem2.a: |- A = ( N Mat R )
  assume cayhamlem2.b: |- B = ( Base ` A )
  assume cayhamlem2.1: |- .1. = ( 1r ` A )
  assume cayhamlem2.m: |- .* = ( .s ` A )
  assume cayhamlem2.e: |- .^ = ( .g ` ( mulGrp ` A ) )
  assume cayhamlem2.r: |- .x. = ( .r ` A )


  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( H e. ( K ^m NN0 ) /\ L e. NN0 ) ) -> ( ( H ` L ) .* ( L .^ M ) ) = ( ( L .^ M ) .x. ( ( H ` L ) .* .1. ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cH
    cK
    cn0
    cmap
    co
    wcel
    #
    cL
    cn0
    wcel
    #
    wa
    #
    wa
    #
    cL
    cM
    c.ex
    co
    #
    cL
    cH
    cfv
    #
    c.1
    c.as
    co
    #
    c.x
    co
    @8
    @9
    cA
    cascl
    cfv
    #
    cfv
    #
    c.x
    co
    #
    @9
    @8
    c.as
    co
    #
    @7
    @10
    @12
    @8
    c.x
    @7
    @12
    @10
    @7
    @9
    cA
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @12
    @10
    wceq
    @7
    @17
    @9
    cK
    wcel
    #
    @6
    @18
    @3
    @4
    cn0
    cK
    cL
    cH
    cH
    cK
    cn0
    elmapi
    ffvelrnda
    adantl
    @3
    @17
    @18
    wb
    @6
    @3
    @16
    cK
    @9
    @3
    cK
    cR
    cbs
    cfv
    @16
    cayhamlem2.k
    @3
    cR
    @15
    cbs
    @0
    @1
    cR
    @15
    wceq
    @2
    cA
    cR
    cN
    ccrg
    cayhamlem2.a
    matsca2
    3adant3
    fveq2d
    syl5req
    eleq2d
    adantr
    mpbird
    #
    @11
    c.as
    c.1
    @15
    @16
    cA
    @9
    @11
    eqid
    #
    @15
    eqid
    #
    @16
    eqid
    #
    cayhamlem2.m
    cayhamlem2.1
    asclval
    syl
    eqcomd
    oveq2d
    @7
    cA
    casa
    wcel
    #
    @17
    @8
    cB
    wcel
    #
    @13
    @14
    wceq
    @3
    @23
    @6
    @0
    @1
    @23
    @2
    cA
    cR
    cN
    cayhamlem2.a
    matassa
    3adant3
    adantr
    @19
    @7
    cA
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @5
    @2
    @24
    @3
    @26
    @6
    @3
    @0
    cR
    crg
    wcel
    #
    wa
    #
    cA
    crg
    wcel
    @26
    @0
    @1
    @28
    @2
    @1
    @27
    @0
    cR
    crngring
    anim2i
    3adant3
    cA
    cR
    cN
    cayhamlem2.a
    matring
    cA
    @25
    @25
    eqid
    #
    ringmgp
    3syl
    adantr
    @3
    @4
    @5
    simprr
    @0
    @1
    @2
    @6
    simpl3
    cB
    c.ex
    @25
    cL
    cM
    cB
    cA
    @25
    @29
    cayhamlem2.b
    mgpbas
    cayhamlem2.e
    mulgnn0cl
    syl3anc
    @11
    @9
    c.as
    c.x
    @15
    @16
    cB
    cA
    @8
    @20
    @21
    @22
    cayhamlem2.b
    cayhamlem2.r
    cayhamlem2.m
    asclmul2
    syl3anc
    eqtr2d
end
