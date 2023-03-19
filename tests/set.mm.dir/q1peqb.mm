include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cvv.mm"
include "co.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "elex.mm"
include "adantr.mm"
include "a1i.mm"
include "ovex.mm"
include "eleq1.mm"
include "mpbii.mm"
include "wb.mm"
include "cv.mm"
include "cio.mm"
include "simpr.mm"
include "weu.mm"
include "wreu.mm"
include "cui.mm"
include "c0g.mm"
include "eqid.mm"
include "simp1.mm"
include "simp2.mm"
include "uc1pcl.mm"
include "3ad2ant3.mm"
include "wne.mm"
include "uc1pn0.mm"
include "cco1.mm"
include "uc1pldg.mm"
include "ply1divalg2.mm"
include "df-reu.mm"
include "sylib.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "adantl.mm"
include "iota2d.mm"
include "crio.mm"
include "q1pval.mm"
include "syl2anc.mm"
include "df-riota.mm"
include "syl6eq.mm"
include "eqeq1d.mm"
include "bitr4d.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem q1peqb
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume q1pval.q: |- Q = ( quot1p ` R )
  assume q1pval.p: |- P = ( Poly1 ` R )
  assume q1pval.b: |- B = ( Base ` P )
  assume q1pval.d: |- D = ( deg1 ` R )
  assume q1pval.m: |- .- = ( -g ` P )
  assume q1pval.t: |- .x. = ( .r ` P )
  assume q1peqb.c: |- C = ( Unic1p ` R )


  assert |- ( ( R e. Ring /\ F e. B /\ G e. C ) -> ( ( X e. B /\ ( D ` ( F .- ( X .x. G ) ) ) < ( D ` G ) ) <-> ( F Q G ) = X ) )

  proof
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    cG
    cC
    wcel
    #
    w3a
    #
    cX
    cvv
    wcel
    #
    cX
    cB
    wcel
    #
    cF
    cX
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
    wa
    #
    cF
    cG
    cQ
    co
    #
    cX
    wceq
    #
    @11
    @4
    wi
    @3
    @5
    @4
    @10
    cX
    cB
    elex
    adantr
    a1i
    @13
    @4
    wi
    @3
    @13
    @12
    cvv
    wcel
    @4
    cF
    cG
    cQ
    ovex
    @12
    cX
    cvv
    eleq1
    mpbii
    a1i
    @3
    @4
    @11
    @13
    wb
    @3
    @4
    wa
    #
    @11
    vq
    cv
    #
    cB
    wcel
    #
    cF
    @15
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
    @9
    clt
    wbr
    #
    wa
    #
    vq
    cio
    #
    cX
    wceq
    @13
    @14
    @21
    @11
    vq
    cX
    cvv
    @3
    @4
    simpr
    @3
    @21
    vq
    weu
    #
    @4
    @3
    @20
    vq
    cB
    wreu
    @23
    @3
    cB
    cD
    cP
    cR
    c.x
    cR
    cui
    cfv
    #
    cF
    cG
    c.mi
    cP
    c0g
    cfv
    #
    vq
    q1pval.p
    q1pval.d
    q1pval.b
    q1pval.m
    @25
    eqid
    #
    q1pval.t
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    #
    @2
    @0
    cG
    cB
    wcel
    #
    @1
    cB
    cC
    cP
    cR
    cG
    q1pval.p
    q1pval.b
    q1peqb.c
    uc1pcl
    3ad2ant3
    #
    @2
    @0
    cG
    @25
    wne
    @1
    cC
    cP
    cR
    cG
    @25
    q1pval.p
    @26
    q1peqb.c
    uc1pn0
    3ad2ant3
    @2
    @0
    @9
    cG
    cco1
    cfv
    cfv
    @24
    wcel
    @1
    cC
    cD
    cR
    @24
    cG
    q1pval.d
    @24
    eqid
    #
    q1peqb.c
    uc1pldg
    3ad2ant3
    @30
    ply1divalg2
    @20
    vq
    cB
    df-reu
    sylib
    adantr
    @15
    cX
    wceq
    #
    @21
    @11
    wb
    @14
    @31
    @16
    @5
    @20
    @10
    @15
    cX
    cB
    eleq1
    @31
    @19
    @8
    @9
    clt
    @31
    @18
    @7
    cD
    @31
    @17
    @6
    cF
    c.mi
    @15
    cX
    cG
    c.x
    oveq1
    oveq2d
    fveq2d
    breq1d
    anbi12d
    adantl
    iota2d
    @14
    @12
    @22
    cX
    @3
    @12
    @22
    wceq
    @4
    @3
    @12
    @20
    vq
    cB
    crio
    #
    @22
    @3
    @1
    @28
    @12
    @32
    wceq
    @27
    @29
    cB
    cD
    cP
    cQ
    cR
    c.x
    cF
    cG
    c.mi
    vq
    q1pval.q
    q1pval.p
    q1pval.b
    q1pval.d
    q1pval.m
    q1pval.t
    q1pval
    syl2anc
    @20
    vq
    cB
    df-riota
    syl6eq
    adantr
    eqeq1d
    bitr4d
    ex
    pm5.21ndd
end
