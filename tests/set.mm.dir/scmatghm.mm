include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "cbs.mm"
include "eqid.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "adantl.mm"
include "csubg.mm"
include "c0g.mm"
include "scmatsgrp.mm"
include "subggrp.mm"
include "syl.mm"
include "wf.mm"
include "scmatf.mm"
include "scmatstrbas.mm"
include "feq3d.mm"
include "mpbird.mm"
include "cv.mm"
include "co.mm"
include "csca.mm"
include "wceq.mm"
include "matsca2.mm"
include "cvv.mm"
include "cscmat.mm"
include "ovex.mm"
include "eqeltri.mm"
include "resssca.mm"
include "mp1i.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "oveq1d.mm"
include "adantr.mm"
include "clmod.mm"
include "clss.mm"
include "matlmod.mm"
include "scmatlss.mm"
include "lsslmod.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "adantrd.mm"
include "imp.mm"
include "adantld.mm"
include "cur.mm"
include "scmatid.mm"
include "a1i.mm"
include "3eltr4d.mm"
include "cvsca.mm"
include "ressvsca.mm"
include "ax-mp.mm"
include "lmodvsdir.mm"
include "syl13anc.mm"
include "simpr.mm"
include "w3a.mm"
include "anim1i.mm"
include "3anass.mm"
include "sylibr.mm"
include "ringacl.mm"
include "scmatrhmval.mm"
include "ad2ant2lr.mm"
include "ad2ant2l.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "isghmd.mm"

theorem scmatghm
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cR: class R
  let cS: class S
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
  assume scmatghm.s: |- S = ( A |`s C )

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
  disjoint S y
  disjoint S z
  assert |- ( ( N e. Fin /\ R e. Ring ) -> F e. ( R GrpHom S ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    vy
    vz
    cR
    cplusg
    cfv
    #
    cS
    cplusg
    cfv
    #
    cR
    cS
    cF
    cK
    cS
    cbs
    cfv
    #
    scmatrhmval.k
    @5
    eqid
    #
    @3
    eqid
    #
    @4
    eqid
    #
    @1
    cR
    cgrp
    wcel
    @0
    cR
    ringgrp
    adantl
    @2
    cC
    cA
    csubg
    cfv
    wcel
    cS
    cgrp
    wcel
    cA
    cA
    cbs
    cfv
    #
    cR
    cC
    cK
    cN
    cR
    c0g
    cfv
    #
    scmatrhmval.a
    @9
    eqid
    #
    scmatrhmval.k
    @10
    eqid
    #
    scmatrhmval.c
    scmatsgrp
    cC
    cA
    cS
    scmatghm.s
    subggrp
    syl
    @2
    cK
    @5
    cF
    wf
    cK
    cC
    cF
    wf
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
    @2
    @5
    cC
    cF
    cK
    cA
    cC
    cR
    cS
    cN
    scmatrhmval.a
    scmatrhmval.c
    scmatghm.s
    scmatstrbas
    #
    feq3d
    mpbird
    @2
    vy
    cv
    #
    cK
    wcel
    #
    vz
    cv
    #
    cK
    wcel
    #
    wa
    #
    wa
    #
    @14
    @16
    @3
    co
    #
    c.1
    c.as
    co
    #
    @14
    c.1
    c.as
    co
    #
    @16
    c.1
    c.as
    co
    #
    @4
    co
    #
    @20
    cF
    cfv
    #
    @14
    cF
    cfv
    #
    @16
    cF
    cfv
    #
    @4
    co
    @19
    @21
    @14
    @16
    cS
    csca
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    c.1
    c.as
    co
    #
    @24
    @2
    @21
    @31
    wceq
    @18
    @2
    @20
    @30
    c.1
    c.as
    @2
    @3
    @29
    @14
    @16
    @2
    cR
    @28
    cplusg
    @2
    cR
    cA
    csca
    cfv
    #
    @28
    cA
    cR
    cN
    crg
    scmatrhmval.a
    matsca2
    cC
    cvv
    wcel
    #
    @32
    @28
    wceq
    @2
    cC
    cN
    cR
    cscmat
    co
    cvv
    scmatrhmval.c
    cN
    cR
    cscmat
    ovex
    eqeltri
    #
    cC
    @32
    cA
    cS
    cvv
    scmatghm.s
    @32
    eqid
    resssca
    mp1i
    eqtrd
    #
    fveq2d
    oveqd
    oveq1d
    adantr
    @19
    cS
    clmod
    wcel
    #
    @14
    @28
    cbs
    cfv
    #
    wcel
    #
    @16
    @37
    wcel
    #
    c.1
    @5
    wcel
    #
    @31
    @24
    wceq
    @2
    @36
    @18
    @2
    cA
    clmod
    wcel
    cC
    cA
    clss
    cfv
    #
    wcel
    @36
    cA
    cR
    cN
    scmatrhmval.a
    matlmod
    cA
    cR
    cC
    cN
    scmatrhmval.a
    scmatrhmval.c
    scmatlss
    @41
    cC
    cA
    cS
    scmatghm.s
    @41
    eqid
    lsslmod
    syl2anc
    adantr
    @2
    @18
    @38
    @2
    @15
    @38
    @17
    @2
    @15
    @38
    @2
    cK
    @37
    @14
    @2
    cK
    cR
    cbs
    cfv
    @37
    scmatrhmval.k
    @2
    cR
    @28
    cbs
    @35
    fveq2d
    syl5eq
    #
    eleq2d
    biimpd
    adantrd
    imp
    @2
    @18
    @39
    @2
    @17
    @39
    @15
    @2
    @17
    @39
    @2
    cK
    @37
    @16
    @42
    eleq2d
    biimpd
    adantld
    imp
    @2
    @40
    @18
    @2
    cA
    cur
    cfv
    #
    cC
    c.1
    @5
    cA
    @9
    cR
    cC
    cK
    cN
    @10
    scmatrhmval.a
    @11
    scmatrhmval.k
    @12
    scmatrhmval.c
    scmatid
    c.1
    @43
    wceq
    @2
    scmatrhmval.o
    a1i
    @13
    3eltr4d
    adantr
    @4
    @29
    @14
    @16
    c.as
    @28
    @37
    @5
    cS
    c.1
    @6
    @8
    @28
    eqid
    @33
    c.as
    cS
    cvsca
    cfv
    wceq
    @34
    cC
    c.as
    cA
    cS
    cvv
    scmatghm.s
    scmatrhmval.t
    ressvsca
    ax-mp
    @37
    eqid
    @29
    eqid
    lmodvsdir
    syl13anc
    eqtrd
    @19
    @1
    @20
    cK
    wcel
    #
    @25
    @21
    wceq
    @2
    @1
    @18
    @0
    @1
    simpr
    #
    adantr
    @19
    @1
    @15
    @17
    w3a
    #
    @44
    @19
    @1
    @18
    wa
    @46
    @2
    @1
    @18
    @45
    anim1i
    @1
    @15
    @17
    3anass
    sylibr
    cK
    @3
    cR
    @14
    @16
    scmatrhmval.k
    @7
    ringacl
    syl
    vx
    cA
    cR
    c.1
    cF
    c.as
    cK
    cN
    crg
    @20
    scmatrhmval.k
    scmatrhmval.a
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.f
    scmatrhmval
    syl2anc
    @19
    @26
    @22
    @27
    @23
    @4
    @1
    @15
    @26
    @22
    wceq
    @0
    @17
    vx
    cA
    cR
    c.1
    cF
    c.as
    cK
    cN
    crg
    @14
    scmatrhmval.k
    scmatrhmval.a
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.f
    scmatrhmval
    ad2ant2lr
    @1
    @17
    @27
    @23
    wceq
    @0
    @15
    vx
    cA
    cR
    c.1
    cF
    c.as
    cK
    cN
    crg
    @16
    scmatrhmval.k
    scmatrhmval.a
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.f
    scmatrhmval
    ad2ant2l
    oveq12d
    3eqtr4d
    isghmd
end
