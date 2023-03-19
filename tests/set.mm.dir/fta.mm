include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cdgr.mm"
include "cn.mm"
include "wa.mm"
include "cv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cc.mm"
include "wral.mm"
include "wrex.mm"
include "cc0.mm"
include "wceq.mm"
include "clt.mm"
include "wi.mm"
include "crp.mm"
include "ccoe.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cif.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "ftalem2.mm"
include "crab.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "simpll.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "fveq2.mm"
include "breq2d.mm"
include "fveq2d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "ftalem3.mm"
include "rexlimddv.mm"
include "wne.mm"
include "wn.mm"
include "ftalem7.mm"
include "expr.mm"
include "necon4ad.mm"
include "reximdva.mm"
include "mpd.mm"

theorem fta
  let vz: setvar z
  let cS: class S
  let cF: class F
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y

  disjoint F z
  disjoint S z
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint S r
  disjoint S s
  disjoint S x
  disjoint S y
  assert |- ( ( F e. ( Poly ` S ) /\ ( deg ` F ) e. NN ) -> E. z e. CC ( F ` z ) = 0 )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cF
    cdgr
    cfv
    #
    cn
    wcel
    #
    wa
    #
    vz
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    vx
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    cle
    wbr
    vx
    cc
    wral
    #
    vz
    cc
    wrex
    #
    @5
    cc0
    wceq
    #
    vz
    cc
    wrex
    @3
    vr
    cv
    #
    vy
    cv
    #
    cabs
    cfv
    #
    clt
    wbr
    #
    cc0
    cF
    cfv
    cabs
    cfv
    #
    @13
    cF
    cfv
    #
    cabs
    cfv
    #
    clt
    wbr
    #
    wi
    #
    vy
    cc
    wral
    #
    @10
    vr
    crp
    @3
    vy
    cF
    ccoe
    cfv
    #
    cS
    @16
    @1
    @22
    cfv
    cabs
    cfv
    c2
    cdiv
    co
    cdiv
    co
    #
    c1
    vs
    cv
    #
    cle
    wbr
    @24
    c1
    cif
    #
    @23
    cle
    wbr
    @23
    @25
    cif
    #
    cF
    @1
    vs
    vr
    @22
    eqid
    #
    @1
    eqid
    #
    @0
    @2
    simpl
    @0
    @2
    simpr
    @26
    eqid
    @23
    eqid
    ftalem2
    @3
    @12
    crp
    wcel
    #
    @21
    wa
    #
    wa
    #
    vx
    vs
    vz
    @22
    @24
    cabs
    cfv
    @12
    cle
    wbr
    vs
    cc
    crab
    #
    @12
    cS
    cF
    ccnfld
    ctopn
    cfv
    #
    @1
    @27
    @28
    @0
    @2
    @30
    simpll
    @0
    @2
    @30
    simplr
    @32
    eqid
    @33
    eqid
    @3
    @29
    @21
    simprl
    @31
    @21
    @12
    @6
    cabs
    cfv
    #
    clt
    wbr
    #
    @16
    @8
    clt
    wbr
    #
    wi
    #
    vx
    cc
    wral
    @3
    @29
    @21
    simprr
    @20
    @37
    vy
    vx
    cc
    @13
    @6
    wceq
    #
    @15
    @35
    @19
    @36
    @38
    @14
    @34
    @12
    clt
    @13
    @6
    cabs
    fveq2
    breq2d
    @38
    @18
    @8
    @16
    clt
    @38
    @17
    @7
    cabs
    @13
    @6
    cF
    fveq2
    fveq2d
    breq2d
    imbi12d
    cbvralv
    sylib
    ftalem3
    rexlimddv
    @3
    @9
    @11
    vz
    cc
    @3
    @4
    cc
    wcel
    #
    wa
    @9
    @5
    cc0
    @3
    @39
    @5
    cc0
    wne
    #
    @9
    wn
    @3
    @39
    @40
    wa
    #
    wa
    vx
    @22
    cS
    cF
    @1
    @4
    @27
    @28
    @0
    @2
    @41
    simpll
    @0
    @2
    @41
    simplr
    @3
    @39
    @40
    simprl
    @3
    @39
    @40
    simprr
    ftalem7
    expr
    necon4ad
    reximdva
    mpd
end
