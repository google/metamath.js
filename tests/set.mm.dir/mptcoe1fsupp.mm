include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cco1.mm"
include "cvv.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cn0.mm"
include "eqid.mm"
include "coe1fvalcl.mm"
include "adantll.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "csb.mm"
include "cmap.mm"
include "co.mm"
include "cfsupp.mm"
include "crab.mm"
include "simpr.mm"
include "coe1fsupp.mm"
include "elrabi.mm"
include "3syl.mm"
include "jctir.mm"
include "coe1sfi.mm"
include "adantl.mm"
include "fsuppmapnn0ub.mm"
include "sylc.mm"
include "csbfv.mm"
include "syl5eq.mm"
include "exp31.mm"
include "a2d.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "mptnn0fsupp.mm"

theorem mptcoe1fsupp
  let cB: class B
  let cP: class P
  let cR: class R
  let vk: setvar k
  let cM: class M
  let c.0: class .0.
  let vs: setvar s
  let vx: setvar x
  let vc: setvar c
  assume mptcoe1fsupp.p: |- P = ( Poly1 ` R )
  assume mptcoe1fsupp.b: |- B = ( Base ` P )
  assume mptcoe1fsupp.0: |- .0. = ( 0g ` R )

  disjoint B k
  disjoint M k
  disjoint R k
  disjoint B s
  disjoint B x
  disjoint k s
  disjoint k x
  disjoint s x
  disjoint M c
  disjoint M s
  disjoint M x
  disjoint R c
  disjoint R s
  disjoint R x
  disjoint .0. c
  disjoint .0. s
  disjoint .0. x
  assert |- ( ( R e. Ring /\ M e. B ) -> ( k e. NN0 |-> ( ( coe1 ` M ) ` k ) ) finSupp .0. )

  proof
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    wa
    #
    vx
    cR
    cbs
    cfv
    #
    vk
    cv
    #
    cM
    cco1
    cfv
    #
    cfv
    #
    vk
    cvv
    c.0
    vs
    c.0
    cvv
    wcel
    #
    @2
    c.0
    cR
    c0g
    cfv
    cvv
    mptcoe1fsupp.0
    cR
    c0g
    fvex
    eqeltri
    #
    a1i
    @1
    @4
    cn0
    wcel
    @6
    @3
    wcel
    @0
    @5
    cB
    cP
    cR
    cM
    @3
    @4
    @5
    eqid
    #
    mptcoe1fsupp.b
    mptcoe1fsupp.p
    @3
    eqid
    #
    coe1fvalcl
    adantll
    @2
    vs
    cv
    #
    vx
    cv
    #
    clt
    wbr
    #
    @12
    @5
    cfv
    #
    c.0
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    vs
    cn0
    wrex
    #
    @13
    vk
    @12
    @6
    csb
    #
    c.0
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    vs
    cn0
    wrex
    @2
    @5
    @3
    cn0
    cmap
    co
    #
    wcel
    #
    @7
    wa
    @5
    c.0
    cfsupp
    wbr
    #
    @18
    @2
    @24
    @7
    @2
    @1
    @5
    vc
    cv
    c.0
    cfsupp
    wbr
    #
    vc
    @23
    crab
    wcel
    @24
    @0
    @1
    simpr
    @5
    cB
    cP
    cR
    vc
    cM
    @3
    c.0
    @9
    mptcoe1fsupp.b
    mptcoe1fsupp.p
    mptcoe1fsupp.0
    @10
    coe1fsupp
    @26
    vc
    @5
    @23
    elrabi
    3syl
    @8
    jctir
    @1
    @25
    @0
    @5
    cB
    cP
    cR
    cM
    c.0
    @9
    mptcoe1fsupp.b
    mptcoe1fsupp.p
    mptcoe1fsupp.0
    coe1sfi
    adantl
    vx
    @3
    vs
    @5
    cvv
    c.0
    fsuppmapnn0ub
    sylc
    @2
    @17
    @22
    vs
    cn0
    @2
    @11
    cn0
    wcel
    wa
    #
    @16
    @21
    vx
    cn0
    @27
    @12
    cn0
    wcel
    wa
    #
    @13
    @15
    @20
    @28
    @13
    @15
    @20
    @28
    @13
    wa
    #
    @15
    wa
    @19
    @14
    c.0
    vk
    @12
    @5
    csbfv
    @29
    @15
    simpr
    syl5eq
    exp31
    a2d
    ralimdva
    reximdva
    mpd
    mptnn0fsupp
end
