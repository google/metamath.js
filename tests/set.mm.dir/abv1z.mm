include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "cr.mm"
include "cbs.mm"
include "crg.mm"
include "abvrcl.mm"
include "eqid.mm"
include "ringidcl.mm"
include "syl.mm"
include "abvcl.mm"
include "mpdan.mm"
include "adantr.mm"
include "recnd.mm"
include "cc0.mm"
include "simpl.mm"
include "simpr.mm"
include "abvne0.mm"
include "syl3anc.mm"
include "divcan3d.mm"
include "cmulr.mm"
include "wceq.mm"
include "ringlidm.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "abvmul.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "dividd.mm"

theorem abv1z
  let cA: class A
  let cR: class R
  let c.1: class .1.
  let cF: class F
  let c.0: class .0.
  assume abv0.a: |- A = ( AbsVal ` R )
  assume abv1.p: |- .1. = ( 1r ` R )
  assume abv1z.z: |- .0. = ( 0g ` R )


  assert |- ( ( F e. A /\ .1. =/= .0. ) -> ( F ` .1. ) = 1 )

  proof
    cF
    cA
    wcel
    #
    c.1
    c.0
    wne
    #
    wa
    #
    c.1
    cF
    cfv
    #
    @3
    cmul
    co
    #
    @3
    cdiv
    co
    #
    @3
    c1
    @2
    @3
    @3
    @2
    @3
    @0
    @3
    cr
    wcel
    #
    @1
    @0
    c.1
    cR
    cbs
    cfv
    #
    wcel
    #
    @6
    @0
    cR
    crg
    wcel
    #
    @8
    cA
    cR
    cF
    abv0.a
    abvrcl
    #
    @7
    cR
    c.1
    @7
    eqid
    #
    abv1.p
    ringidcl
    syl
    #
    cA
    @7
    cR
    cF
    c.1
    abv0.a
    @11
    abvcl
    mpdan
    adantr
    recnd
    #
    @13
    @2
    @0
    @8
    @1
    @3
    cc0
    wne
    @0
    @1
    simpl
    #
    @0
    @8
    @1
    @12
    adantr
    #
    @0
    @1
    simpr
    cA
    @7
    cR
    cF
    c.1
    c.0
    abv0.a
    @11
    abv1z.z
    abvne0
    syl3anc
    #
    divcan3d
    @2
    @3
    @3
    cdiv
    co
    @5
    c1
    @2
    @3
    @4
    @3
    cdiv
    @2
    c.1
    c.1
    cR
    cmulr
    cfv
    #
    co
    #
    cF
    cfv
    #
    @3
    @4
    @2
    @18
    c.1
    cF
    @2
    @9
    @8
    @18
    c.1
    wceq
    @0
    @9
    @1
    @10
    adantr
    @15
    @7
    cR
    @17
    c.1
    c.1
    @11
    @17
    eqid
    #
    abv1.p
    ringlidm
    syl2anc
    fveq2d
    @2
    @0
    @8
    @8
    @19
    @4
    wceq
    @14
    @15
    @15
    cA
    @7
    cR
    @17
    cF
    c.1
    c.1
    abv0.a
    @11
    @20
    abvmul
    syl3anc
    eqtr3d
    oveq1d
    @2
    @3
    @13
    @16
    dividd
    eqtr3d
    eqtr3d
end
