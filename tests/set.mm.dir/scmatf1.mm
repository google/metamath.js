include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "crg.mm"
include "w3a.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "scmatf.mm"
include "3adant2.mm"
include "wa.mm"
include "co.mm"
include "wb.mm"
include "simpr.mm"
include "simpl.mm"
include "scmatrhmval.mm"
include "syl2an.mm"
include "eqeq12d.mm"
include "3adantl2.mm"
include "cbs.mm"
include "matring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "syl.mm"
include "anim12ci.mm"
include "matvscl.mm"
include "syldan.mm"
include "jca.mm"
include "eqmat.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "difsnid.mm"
include "eqcomd.mm"
include "adantl.mm"
include "raleqdv.mm"
include "oveq2.mm"
include "ralunsn.mm"
include "c0g.mm"
include "cif.mm"
include "anim2i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "id.mm"
include "scmatscmide.mm"
include "iftruei.mm"
include "syl6eq.mm"
include "anbi2d.mm"
include "3bitrd.mm"
include "ralbidva.mm"
include "r19.26.mm"
include "rspn0.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "com12.mm"
include "sylbi.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem scmatf1
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cR: class R
  let c.1: class .1.
  let cF: class F
  let c.as: class .*
  let cK: class K
  let cN: class N
  let cV: class V
  let cX: class X
  let vc: setvar c
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let vj: setvar j
  assume scmatrhmval.k: |- K = ( Base ` R )
  assume scmatrhmval.a: |- A = ( N Mat R )
  assume scmatrhmval.o: |- .1. = ( 1r ` A )
  assume scmatrhmval.t: |- .* = ( .s ` A )
  assume scmatrhmval.f: |- F = ( x e. K |-> ( x .* .1. ) )
  assume scmatrhmval.c: |- C = ( N ScMat R )

  disjoint K x
  disjoint R x
  disjoint .1. x
  disjoint .* x
  disjoint C x
  disjoint N x
  disjoint V x
  disjoint X x
  disjoint K c
  disjoint N c
  disjoint R c
  disjoint X c
  disjoint .* c
  disjoint .1. c
  disjoint C c
  disjoint C y
  disjoint c y
  disjoint F c
  disjoint F y
  disjoint K y
  disjoint N y
  disjoint c x
  disjoint x y
  disjoint R y
  disjoint F z
  disjoint K i
  disjoint K j
  disjoint K z
  disjoint i j
  disjoint i z
  disjoint j z
  disjoint N i
  disjoint N j
  disjoint N z
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint x z
  disjoint y z
  disjoint R i
  disjoint R j
  disjoint R z
  disjoint .1. i
  disjoint .1. j
  disjoint .* i
  disjoint .* j
  assert |- ( ( N e. Fin /\ N =/= (/) /\ R e. Ring ) -> F : K -1-1-> C )

  proof
    cN
    cfn
    wcel
    #
    cN
    c0
    wne
    #
    cR
    crg
    wcel
    #
    w3a
    #
    cK
    cC
    cF
    wf
    #
    vy
    cv
    #
    cF
    cfv
    #
    vz
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @5
    @7
    wceq
    #
    wi
    #
    vz
    cK
    wral
    vy
    cK
    wral
    cK
    cC
    cF
    wf1
    @0
    @2
    @4
    @1
    vx
    cA
    cC
    cR
    c.1
    cF
    c.as
    cK
    cN
    scmatrhmval.k
    scmatrhmval.a
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.f
    scmatrhmval.c
    scmatf
    3adant2
    @3
    @11
    vy
    vz
    cK
    cK
    @3
    @5
    cK
    wcel
    #
    @7
    cK
    wcel
    #
    wa
    #
    wa
    #
    @9
    @5
    c.1
    c.as
    co
    #
    @7
    c.1
    c.as
    co
    #
    wceq
    #
    @10
    @0
    @2
    @14
    @9
    @18
    wb
    @1
    @0
    @2
    wa
    #
    @14
    wa
    #
    @6
    @16
    @8
    @17
    @19
    @2
    @12
    @6
    @16
    wceq
    @14
    @0
    @2
    simpr
    #
    @12
    @13
    simpl
    #
    vx
    cA
    cR
    c.1
    cF
    c.as
    cK
    cN
    crg
    @5
    scmatrhmval.k
    scmatrhmval.a
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.f
    scmatrhmval
    syl2an
    @19
    @2
    @13
    @8
    @17
    wceq
    @14
    @21
    @12
    @13
    simpr
    #
    vx
    cA
    cR
    c.1
    cF
    c.as
    cK
    cN
    crg
    @7
    scmatrhmval.k
    scmatrhmval.a
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.f
    scmatrhmval
    syl2an
    eqeq12d
    3adantl2
    @15
    @18
    vi
    cv
    #
    vj
    cv
    #
    @16
    co
    #
    @24
    @25
    @17
    co
    #
    wceq
    #
    vj
    cN
    wral
    #
    vi
    cN
    wral
    #
    @10
    @15
    @16
    cA
    cbs
    cfv
    #
    wcel
    #
    @17
    @31
    wcel
    #
    wa
    #
    @18
    @30
    wb
    @0
    @2
    @14
    @34
    @1
    @20
    @32
    @33
    @19
    @14
    @12
    c.1
    @31
    wcel
    #
    wa
    @32
    @19
    @35
    @14
    @12
    @19
    cA
    crg
    wcel
    @35
    cA
    cR
    cN
    scmatrhmval.a
    matring
    @31
    cA
    c.1
    @31
    eqid
    #
    scmatrhmval.o
    ringidcl
    syl
    #
    @22
    anim12ci
    cA
    @31
    @5
    cR
    c.as
    cK
    cN
    c.1
    scmatrhmval.k
    scmatrhmval.a
    @36
    scmatrhmval.t
    matvscl
    syldan
    @19
    @14
    @13
    @35
    wa
    @33
    @19
    @35
    @14
    @13
    @37
    @23
    anim12ci
    cA
    @31
    @7
    cR
    c.as
    cK
    cN
    c.1
    scmatrhmval.k
    scmatrhmval.a
    @36
    scmatrhmval.t
    matvscl
    syldan
    jca
    3adantl2
    cA
    @31
    cR
    vi
    vj
    cN
    @16
    @17
    scmatrhmval.a
    @36
    eqmat
    syl
    @15
    @30
    @28
    vj
    cN
    @24
    csn
    #
    cdif
    #
    wral
    #
    @10
    wa
    #
    vi
    cN
    wral
    #
    @10
    @0
    @2
    @14
    @30
    @42
    wb
    @1
    @20
    @29
    @41
    vi
    cN
    @20
    @24
    cN
    wcel
    #
    wa
    #
    @29
    @28
    vj
    @39
    @38
    cun
    #
    wral
    #
    @40
    @24
    @24
    @16
    co
    #
    @24
    @24
    @17
    co
    #
    wceq
    #
    wa
    #
    @41
    @44
    @28
    vj
    cN
    @45
    @43
    cN
    @45
    wceq
    @20
    @43
    @45
    cN
    cN
    @24
    difsnid
    eqcomd
    adantl
    raleqdv
    @43
    @46
    @50
    wb
    @20
    @28
    @49
    vj
    @39
    @24
    cN
    @25
    @24
    wceq
    @26
    @47
    @27
    @48
    @25
    @24
    @24
    @16
    oveq2
    @25
    @24
    @24
    @17
    oveq2
    eqeq12d
    ralunsn
    adantl
    @44
    @49
    @10
    @40
    @44
    @47
    @5
    @48
    @7
    @44
    @47
    @24
    @24
    wceq
    #
    @5
    cR
    c0g
    cfv
    #
    cif
    #
    @5
    @20
    @0
    @2
    @12
    w3a
    #
    @43
    @43
    wa
    #
    @47
    @53
    wceq
    @43
    @20
    @19
    @12
    wa
    @54
    @14
    @12
    @19
    @22
    anim2i
    @0
    @2
    @12
    df-3an
    sylibr
    @43
    @43
    @43
    @43
    id
    #
    @56
    jca
    #
    cA
    cK
    @5
    cR
    c.1
    @24
    c.as
    @24
    cN
    @52
    scmatrhmval.a
    scmatrhmval.k
    @52
    eqid
    #
    scmatrhmval.o
    scmatrhmval.t
    scmatscmide
    syl2an
    @51
    @5
    @52
    @24
    eqid
    #
    iftruei
    syl6eq
    @44
    @48
    @51
    @7
    @52
    cif
    #
    @7
    @20
    @0
    @2
    @13
    w3a
    #
    @55
    @48
    @60
    wceq
    @43
    @20
    @19
    @13
    wa
    @61
    @14
    @13
    @19
    @23
    anim2i
    @0
    @2
    @13
    df-3an
    sylibr
    @57
    cA
    cK
    @7
    cR
    c.1
    @24
    c.as
    @24
    cN
    @52
    scmatrhmval.a
    scmatrhmval.k
    @58
    scmatrhmval.o
    scmatrhmval.t
    scmatscmide
    syl2an
    @51
    @7
    @52
    @59
    iftruei
    syl6eq
    eqeq12d
    anbi2d
    3bitrd
    ralbidva
    3adantl2
    @42
    @15
    @10
    @42
    @40
    vi
    cN
    wral
    #
    @10
    vi
    cN
    wral
    #
    wa
    @15
    @10
    wi
    #
    @40
    @10
    vi
    cN
    r19.26
    @63
    @64
    @62
    @15
    @63
    @10
    @3
    @63
    @10
    wi
    #
    @14
    @1
    @0
    @65
    @2
    @10
    vi
    cN
    rspn0
    3ad2ant2
    adantr
    com12
    adantl
    sylbi
    com12
    sylbid
    sylbid
    sylbid
    ralrimivva
    vy
    vz
    cK
    cC
    cF
    dff13
    sylanbrc
end
