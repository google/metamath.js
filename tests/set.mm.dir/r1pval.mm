include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cpl1.mm"
include "elbasfv.mm"
include "adantr.mm"
include "cr1p.mm"
include "cfv.mm"
include "cbs.mm"
include "cq1p.mm"
include "cmulr.mm"
include "csg.mm"
include "csb.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "csbeq1d.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "simpr.mm"
include "eqidd.mm"
include "oveqd.mm"
include "oveq123d.mm"
include "mpt2eq123dv.mm"
include "csbied.mm"
include "eqtrd.mm"
include "df-r1p.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"
include "simpl.mm"
include "oveq12.mm"
include "oveq12d.mm"
include "adantl.mm"
include "ovexd.mm"
include "ovmpt2d.mm"

theorem r1pval
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let cE: class E
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vr: setvar r
  assume r1pval.e: |- E = ( rem1p ` R )
  assume r1pval.p: |- P = ( Poly1 ` R )
  assume r1pval.b: |- B = ( Base ` P )
  assume r1pval.q: |- Q = ( quot1p ` R )
  assume r1pval.t: |- .x. = ( .r ` P )
  assume r1pval.m: |- .- = ( -g ` P )


  assert |- ( ( F e. B /\ G e. B ) -> ( F E G ) = ( F .- ( ( F Q G ) .x. G ) ) )

  proof
    cF
    cB
    wcel
    #
    cG
    cB
    wcel
    #
    wa
    #
    vf
    vg
    cF
    cG
    cB
    cB
    vf
    cv
    #
    @3
    vg
    cv
    #
    cQ
    co
    #
    @4
    c.x
    co
    #
    c.mi
    co
    #
    cF
    cF
    cG
    cQ
    co
    #
    cG
    c.x
    co
    #
    c.mi
    co
    #
    cE
    cvv
    @2
    cR
    cvv
    wcel
    #
    cE
    vf
    vg
    cB
    cB
    @7
    cmpt2
    #
    wceq
    @0
    @11
    @1
    cB
    cP
    cpl1
    cF
    cR
    r1pval.p
    r1pval.b
    elbasfv
    adantr
    @11
    cE
    cR
    cr1p
    cfv
    @12
    r1pval.e
    vr
    cR
    vb
    vr
    cv
    #
    cpl1
    cfv
    #
    cbs
    cfv
    #
    vf
    vg
    vb
    cv
    #
    @16
    @3
    @3
    @4
    @13
    cq1p
    cfv
    #
    co
    #
    @4
    @14
    cmulr
    cfv
    #
    co
    #
    @14
    csg
    cfv
    #
    co
    #
    cmpt2
    #
    csb
    #
    @12
    cvv
    cr1p
    @13
    cR
    wceq
    #
    @24
    vb
    cB
    @23
    csb
    @12
    @25
    vb
    @15
    cB
    @23
    @25
    @15
    cP
    cbs
    cfv
    #
    cB
    @25
    @14
    cP
    cbs
    @25
    @14
    cR
    cpl1
    cfv
    cP
    @13
    cR
    cpl1
    fveq2
    r1pval.p
    syl6eqr
    #
    fveq2d
    r1pval.b
    syl6eqr
    csbeq1d
    @25
    vb
    cB
    @23
    @12
    cvv
    cB
    cvv
    wcel
    @25
    cB
    @26
    cvv
    r1pval.b
    cP
    cbs
    fvex
    eqeltri
    #
    a1i
    @25
    @16
    cB
    wceq
    #
    wa
    vf
    vg
    @16
    @16
    @22
    cB
    cB
    @7
    @25
    @29
    simpr
    #
    @30
    @25
    @22
    @7
    wceq
    @29
    @25
    @3
    @3
    @20
    @6
    @21
    c.mi
    @25
    @21
    cP
    csg
    cfv
    c.mi
    @25
    @14
    cP
    csg
    @27
    fveq2d
    r1pval.m
    syl6eqr
    @25
    @3
    eqidd
    @25
    @18
    @5
    @4
    @4
    @19
    c.x
    @25
    @19
    cP
    cmulr
    cfv
    c.x
    @25
    @14
    cP
    cmulr
    @27
    fveq2d
    r1pval.t
    syl6eqr
    @25
    @17
    cQ
    @3
    @4
    @25
    @17
    cR
    cq1p
    cfv
    cQ
    @13
    cR
    cq1p
    fveq2
    r1pval.q
    syl6eqr
    oveqd
    @25
    @4
    eqidd
    oveq123d
    oveq123d
    adantr
    mpt2eq123dv
    csbied
    eqtrd
    vf
    vg
    vr
    vb
    df-r1p
    vf
    vg
    cB
    cB
    @7
    @28
    @28
    mpt2ex
    fvmpt
    syl5eq
    syl
    @3
    cF
    wceq
    #
    @4
    cG
    wceq
    #
    wa
    #
    @7
    @10
    wceq
    @2
    @33
    @3
    cF
    @6
    @9
    c.mi
    @31
    @32
    simpl
    @33
    @5
    @8
    @4
    cG
    c.x
    @3
    cF
    @4
    cG
    cQ
    oveq12
    @31
    @32
    simpr
    oveq12d
    oveq12d
    adantl
    @0
    @1
    simpl
    @0
    @1
    simpr
    @2
    cF
    @9
    c.mi
    ovexd
    ovmpt2d
end
