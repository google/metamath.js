include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cif.mm"
include "oveqi.mm"
include "cbs.mm"
include "ply1ring.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "anim2i.mm"
include "3adant3.mm"
include "eqid.mm"
include "vr1cl.mm"
include "pmatring.mm"
include "ringidcl.mm"
include "syl.mm"
include "matvscl.mm"
include "syl12anc.mm"
include "mat2pmatbas.mm"
include "simpr.mm"
include "matsubgcell.mm"
include "syl121anc.mm"
include "syl5eq.mm"
include "cv.mm"
include "cvv.mm"
include "cur.mm"
include "cmpt2.mm"
include "a1i.mm"
include "oveq2d.mm"
include "simpl.mm"
include "adantl.mm"
include "3jca.mm"
include "matsc.mm"
include "eqtrd.mm"
include "eqeq12.mm"
include "ifbid.mm"
include "simprl.mm"
include "cv1.mm"
include "fvex.mm"
include "eqeltri.mm"
include "c0g.mm"
include "ifex.mm"
include "ovmpt2d.mm"
include "oveq1d.mm"
include "ovif.mm"
include "syl6eq.mm"

theorem chmatval
  let cA: class A
  let cB: class B
  let cP: class P
  let c.sm: class .~
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let c.1: class .1.
  let cH: class H
  let cI: class I
  let cJ: class J
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  assume chmatcl.a: |- A = ( N Mat R )
  assume chmatcl.b: |- B = ( Base ` A )
  assume chmatcl.p: |- P = ( Poly1 ` R )
  assume chmatcl.y: |- Y = ( N Mat P )
  assume chmatcl.x: |- X = ( var1 ` R )
  assume chmatcl.t: |- T = ( N matToPolyMat R )
  assume chmatcl.s: |- .- = ( -g ` Y )
  assume chmatcl.m: |- .x. = ( .s ` Y )
  assume chmatcl.1: |- .1. = ( 1r ` Y )
  assume chmatcl.h: |- H = ( ( X .x. .1. ) .- ( T ` M ) )
  assume chmatval.s: |- .~ = ( -g ` P )
  assume chmatval.0: |- .0. = ( 0g ` P )


  assert |- ( ( ( N e. Fin /\ R e. Ring /\ M e. B ) /\ ( I e. N /\ J e. N ) ) -> ( I H J ) = if ( I = J , ( X .~ ( I ( T ` M ) J ) ) , ( .0. .~ ( I ( T ` M ) J ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cI
    cN
    wcel
    #
    cJ
    cN
    wcel
    #
    wa
    #
    wa
    #
    cI
    cJ
    cH
    co
    #
    cI
    cJ
    cX
    c.1
    c.x
    co
    #
    co
    #
    cI
    cJ
    cM
    cT
    cfv
    #
    co
    #
    c.sm
    co
    #
    cI
    cJ
    wceq
    #
    cX
    @12
    c.sm
    co
    c.0
    @12
    c.sm
    co
    cif
    #
    @7
    @8
    cI
    cJ
    @9
    @11
    c.mi
    co
    #
    co
    #
    @13
    cH
    @16
    cI
    cJ
    chmatcl.h
    oveqi
    @7
    cP
    crg
    wcel
    #
    @9
    cY
    cbs
    cfv
    #
    wcel
    #
    @11
    @19
    wcel
    #
    @6
    @17
    @13
    wceq
    @3
    @18
    @6
    @1
    @0
    @18
    @2
    cP
    cR
    chmatcl.p
    ply1ring
    #
    3ad2ant2
    adantr
    @3
    @20
    @6
    @3
    @0
    @18
    wa
    #
    cX
    cP
    cbs
    cfv
    #
    wcel
    #
    c.1
    @19
    wcel
    #
    @20
    @0
    @1
    @23
    @2
    @1
    @18
    @0
    @22
    anim2i
    3adant3
    @1
    @0
    @25
    @2
    @24
    cP
    cR
    cX
    chmatcl.x
    chmatcl.p
    @24
    eqid
    #
    vr1cl
    #
    3ad2ant2
    @3
    cY
    crg
    wcel
    #
    @26
    @0
    @1
    @29
    @2
    cY
    cP
    cR
    cN
    chmatcl.p
    chmatcl.y
    pmatring
    3adant3
    @19
    cY
    c.1
    @19
    eqid
    #
    chmatcl.1
    ringidcl
    syl
    cY
    @19
    cX
    cP
    c.x
    @24
    cN
    c.1
    @27
    chmatcl.y
    @30
    chmatcl.m
    matvscl
    syl12anc
    adantr
    @3
    @21
    @6
    cA
    cB
    cY
    cP
    cR
    cT
    cM
    cN
    chmatcl.t
    chmatcl.a
    chmatcl.b
    chmatcl.p
    chmatcl.y
    mat2pmatbas
    adantr
    @3
    @6
    simpr
    cY
    @19
    cP
    c.mi
    cI
    cJ
    c.sm
    cN
    @9
    @11
    chmatcl.y
    @30
    chmatcl.s
    chmatval.s
    matsubgcell
    syl121anc
    syl5eq
    @7
    @13
    @14
    cX
    c.0
    cif
    #
    @12
    c.sm
    co
    @15
    @7
    @10
    @31
    @12
    c.sm
    @7
    vi
    vj
    cI
    cJ
    cN
    cN
    vi
    cv
    #
    vj
    cv
    #
    wceq
    #
    cX
    c.0
    cif
    #
    @31
    @9
    cvv
    @7
    @9
    cX
    cY
    cur
    cfv
    #
    c.x
    co
    #
    vi
    vj
    cN
    cN
    @35
    cmpt2
    #
    @7
    c.1
    @36
    cX
    c.x
    c.1
    @36
    wceq
    @7
    chmatcl.1
    a1i
    oveq2d
    @7
    @0
    @18
    @25
    w3a
    #
    @37
    @38
    wceq
    @3
    @39
    @6
    @0
    @1
    @39
    @2
    @0
    @1
    wa
    @0
    @18
    @25
    @0
    @1
    simpl
    @1
    @18
    @0
    @22
    adantl
    @1
    @25
    @0
    @28
    adantl
    3jca
    3adant3
    adantr
    cY
    cP
    c.x
    vi
    vj
    @24
    cX
    cN
    c.0
    chmatcl.y
    @27
    chmatcl.m
    chmatval.0
    matsc
    syl
    eqtrd
    @32
    cI
    wceq
    @33
    cJ
    wceq
    wa
    #
    @35
    @31
    wceq
    @7
    @40
    @34
    @14
    cX
    c.0
    @32
    cI
    @33
    cJ
    eqeq12
    ifbid
    adantl
    @3
    @4
    @5
    simprl
    @6
    @5
    @3
    @4
    @5
    simpr
    adantl
    @31
    cvv
    wcel
    @7
    @14
    cX
    c.0
    cX
    cR
    cv1
    cfv
    cvv
    chmatcl.x
    cR
    cv1
    fvex
    eqeltri
    c.0
    cP
    c0g
    cfv
    cvv
    chmatval.0
    cP
    c0g
    fvex
    eqeltri
    ifex
    a1i
    ovmpt2d
    oveq1d
    @14
    cX
    c.0
    @12
    c.sm
    ovif
    syl6eq
    eqtrd
end
