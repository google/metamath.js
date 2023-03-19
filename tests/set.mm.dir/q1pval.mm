include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "crio.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cpl1.mm"
include "elbasfv.mm"
include "cq1p.mm"
include "cbs.mm"
include "cmulr.mm"
include "csg.mm"
include "cdg1.mm"
include "csb.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "csbeq1d.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "adantl.mm"
include "simpr.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "eqidd.mm"
include "oveqd.mm"
include "oveq123d.mm"
include "fveq12d.mm"
include "fveq1d.mm"
include "breq12d.mm"
include "riotaeqbidv.mm"
include "mpt2eq123dv.mm"
include "csbied.mm"
include "eqtrd.mm"
include "df-q1p.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"
include "id.mm"
include "oveq2.mm"
include "oveqan12d.mm"
include "fveq2d.mm"
include "riotabidv.mm"
include "simpl.mm"
include "riotaex.mm"
include "ovmpt2d.mm"

theorem q1pval
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let vq: setvar q
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  let vr: setvar r
  assume q1pval.q: |- Q = ( quot1p ` R )
  assume q1pval.p: |- P = ( Poly1 ` R )
  assume q1pval.b: |- B = ( Base ` P )
  assume q1pval.d: |- D = ( deg1 ` R )
  assume q1pval.m: |- .- = ( -g ` P )
  assume q1pval.t: |- .x. = ( .r ` P )

  disjoint B q
  disjoint F q
  disjoint G q
  disjoint P q
  disjoint R q
  disjoint B b
  disjoint B f
  disjoint B g
  disjoint B p
  disjoint B r
  disjoint b f
  disjoint b g
  disjoint b p
  disjoint b q
  disjoint b r
  disjoint f g
  disjoint f p
  disjoint f q
  disjoint f r
  disjoint g p
  disjoint g q
  disjoint g r
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint D b
  disjoint D f
  disjoint D g
  disjoint D p
  disjoint D r
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint .- b
  disjoint .- f
  disjoint .- g
  disjoint .- p
  disjoint .- r
  disjoint P b
  disjoint P f
  disjoint P g
  disjoint P p
  disjoint R b
  disjoint R f
  disjoint R g
  disjoint R p
  disjoint R r
  disjoint .x. b
  disjoint .x. f
  disjoint .x. g
  disjoint .x. p
  disjoint .x. r
  assert |- ( ( F e. B /\ G e. B ) -> ( F Q G ) = ( iota_ q e. B ( D ` ( F .- ( q .x. G ) ) ) < ( D ` G ) ) )

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
    vq
    cv
    #
    vg
    cv
    #
    c.x
    co
    #
    c.mi
    co
    #
    cD
    cfv
    #
    @5
    cD
    cfv
    #
    clt
    wbr
    #
    vq
    cB
    crio
    #
    cF
    @4
    cG
    c.x
    co
    #
    c.mi
    co
    #
    cD
    cfv
    #
    cG
    cD
    cfv
    #
    clt
    wbr
    #
    vq
    cB
    crio
    #
    cQ
    cvv
    @1
    cQ
    vf
    vg
    cB
    cB
    @11
    cmpt2
    #
    wceq
    #
    @0
    @1
    cR
    cvv
    wcel
    #
    @19
    cB
    cP
    cpl1
    cG
    cR
    q1pval.p
    q1pval.b
    elbasfv
    @20
    cQ
    cR
    cq1p
    cfv
    @18
    q1pval.q
    vr
    cR
    vp
    vr
    cv
    #
    cpl1
    cfv
    #
    vb
    vp
    cv
    #
    cbs
    cfv
    #
    vf
    vg
    vb
    cv
    #
    @25
    @3
    @4
    @5
    @23
    cmulr
    cfv
    #
    co
    #
    @23
    csg
    cfv
    #
    co
    #
    @21
    cdg1
    cfv
    #
    cfv
    #
    @5
    @30
    cfv
    #
    clt
    wbr
    #
    vq
    @25
    crio
    #
    cmpt2
    #
    csb
    #
    csb
    #
    @18
    cvv
    cq1p
    @21
    cR
    wceq
    #
    @37
    vp
    cP
    @36
    csb
    @18
    @38
    vp
    @22
    cP
    @36
    @38
    @22
    cR
    cpl1
    cfv
    #
    cP
    @21
    cR
    cpl1
    fveq2
    q1pval.p
    syl6eqr
    csbeq1d
    @38
    vp
    cP
    @36
    @18
    cvv
    cP
    cvv
    wcel
    @38
    cP
    @39
    cvv
    q1pval.p
    cR
    cpl1
    fvex
    eqeltri
    a1i
    @38
    @23
    cP
    wceq
    #
    wa
    #
    @36
    vb
    cB
    @35
    csb
    @18
    @41
    vb
    @24
    cB
    @35
    @41
    @24
    cP
    cbs
    cfv
    #
    cB
    @40
    @24
    @42
    wceq
    @38
    @23
    cP
    cbs
    fveq2
    adantl
    q1pval.b
    syl6eqr
    csbeq1d
    @41
    vb
    cB
    @35
    @18
    cvv
    cB
    cvv
    wcel
    @41
    cB
    @42
    cvv
    q1pval.b
    cP
    cbs
    fvex
    eqeltri
    #
    a1i
    @41
    @25
    cB
    wceq
    #
    wa
    #
    vf
    vg
    @25
    @25
    @34
    cB
    cB
    @11
    @41
    @44
    simpr
    #
    @46
    @45
    @33
    @10
    vq
    @25
    cB
    @46
    @45
    @31
    @8
    @32
    @9
    clt
    @45
    @29
    @7
    @30
    cD
    @45
    @30
    cR
    cdg1
    cfv
    #
    cD
    @38
    @30
    @47
    wceq
    @40
    @44
    @21
    cR
    cdg1
    fveq2
    ad2antrr
    q1pval.d
    syl6eqr
    #
    @45
    @3
    @3
    @27
    @6
    @28
    c.mi
    @45
    @28
    cP
    csg
    cfv
    #
    c.mi
    @40
    @28
    @49
    wceq
    @38
    @44
    @23
    cP
    csg
    fveq2
    ad2antlr
    q1pval.m
    syl6eqr
    @45
    @3
    eqidd
    @45
    @26
    c.x
    @4
    @5
    @45
    @26
    cP
    cmulr
    cfv
    #
    c.x
    @40
    @26
    @50
    wceq
    @38
    @44
    @23
    cP
    cmulr
    fveq2
    ad2antlr
    q1pval.t
    syl6eqr
    oveqd
    oveq123d
    fveq12d
    @45
    @5
    @30
    cD
    @48
    fveq1d
    breq12d
    riotaeqbidv
    mpt2eq123dv
    csbied
    eqtrd
    csbied
    eqtrd
    vf
    vg
    vr
    vq
    vp
    vb
    df-q1p
    vf
    vg
    cB
    cB
    @11
    @43
    @43
    mpt2ex
    fvmpt
    syl5eq
    syl
    adantl
    @3
    cF
    wceq
    #
    @5
    cG
    wceq
    #
    wa
    #
    @11
    @17
    wceq
    @2
    @53
    @10
    @16
    vq
    cB
    @53
    @8
    @14
    @9
    @15
    clt
    @53
    @7
    @13
    cD
    @51
    @52
    @3
    cF
    @6
    @12
    c.mi
    @51
    id
    @5
    cG
    @4
    c.x
    oveq2
    oveqan12d
    fveq2d
    @52
    @9
    @15
    wceq
    @51
    @5
    cG
    cD
    fveq2
    adantl
    breq12d
    riotabidv
    adantl
    @0
    @1
    simpl
    @0
    @1
    simpr
    @17
    cvv
    wcel
    @2
    @16
    vq
    cB
    riotaex
    a1i
    ovmpt2d
end
