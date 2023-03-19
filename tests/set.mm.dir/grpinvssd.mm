include "wcel.mm"
include "cminusg.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cplusg.mm"
include "co.mm"
include "c0g.mm"
include "cv.mm"
include "wral.mm"
include "cgrp.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "sylan.mm"
include "simpr.mm"
include "adantr.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "grplinv.mm"
include "cbs.mm"
include "sselda.mm"
include "syl2anc.mm"
include "grpidssd.mm"
include "eqtr2d.mm"
include "3eqtrd.mm"
include "wb.mm"
include "wss.mm"
include "sseldd.mm"
include "grprcan.mm"
include "syl13anc.mm"
include "mpbid.mm"
include "ex.mm"

theorem grpinvssd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cS: class S
  let cM: class M
  let cX: class X
  assume grpidssd.m: |- ( ph -> M e. Grp )
  assume grpidssd.s: |- ( ph -> S e. Grp )
  assume grpidssd.b: |- B = ( Base ` S )
  assume grpidssd.c: |- ( ph -> B C_ ( Base ` M ) )
  assume grpidssd.o: |- ( ph -> A. x e. B A. y e. B ( x ( +g ` M ) y ) = ( x ( +g ` S ) y ) )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint M x
  disjoint M y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  assert |- ( ph -> ( X e. B -> ( ( invg ` S ) ` X ) = ( ( invg ` M ) ` X ) ) )

  proof
    wph
    cX
    cB
    wcel
    #
    cX
    cS
    cminusg
    cfv
    #
    cfv
    #
    cX
    cM
    cminusg
    cfv
    #
    cfv
    #
    wceq
    #
    wph
    @0
    wa
    #
    @2
    cX
    cM
    cplusg
    cfv
    #
    co
    #
    @4
    cX
    @7
    co
    #
    wceq
    #
    @5
    @6
    @8
    @2
    cX
    cS
    cplusg
    cfv
    #
    co
    #
    cS
    c0g
    cfv
    #
    @9
    @6
    @2
    cB
    wcel
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    @7
    co
    #
    @15
    @16
    @11
    co
    #
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @8
    @12
    wceq
    #
    wph
    cS
    cgrp
    wcel
    #
    @0
    @14
    grpidssd.s
    cB
    cS
    @1
    cX
    grpidssd.b
    @1
    eqid
    #
    grpinvcl
    sylan
    #
    wph
    @0
    simpr
    wph
    @20
    @0
    grpidssd.o
    adantr
    @19
    @21
    @2
    @16
    @7
    co
    #
    @2
    @16
    @11
    co
    #
    wceq
    vx
    vy
    @2
    cX
    cB
    cB
    @15
    @2
    wceq
    @17
    @25
    @18
    @26
    @15
    @2
    @16
    @7
    oveq1
    @15
    @2
    @16
    @11
    oveq1
    eqeq12d
    @16
    cX
    wceq
    @25
    @8
    @26
    @12
    @16
    cX
    @2
    @7
    oveq2
    @16
    cX
    @2
    @11
    oveq2
    eqeq12d
    rspc2va
    syl21anc
    wph
    @22
    @0
    @12
    @13
    wceq
    grpidssd.s
    cB
    @11
    cS
    @1
    cX
    @13
    grpidssd.b
    @11
    eqid
    @13
    eqid
    @23
    grplinv
    sylan
    @6
    @9
    cM
    c0g
    cfv
    #
    @13
    @6
    cM
    cgrp
    wcel
    #
    cX
    cM
    cbs
    cfv
    #
    wcel
    #
    @9
    @27
    wceq
    wph
    @28
    @0
    grpidssd.m
    adantr
    #
    wph
    cB
    @29
    cX
    grpidssd.c
    sselda
    #
    @29
    @7
    cM
    @3
    cX
    @27
    @29
    eqid
    #
    @7
    eqid
    #
    @27
    eqid
    @3
    eqid
    #
    grplinv
    syl2anc
    wph
    @27
    @13
    wceq
    @0
    wph
    vx
    vy
    cB
    cS
    cM
    grpidssd.m
    grpidssd.s
    grpidssd.b
    grpidssd.c
    grpidssd.o
    grpidssd
    adantr
    eqtr2d
    3eqtrd
    @6
    @28
    @2
    @29
    wcel
    @4
    @29
    wcel
    #
    @30
    @10
    @5
    wb
    @31
    @6
    cB
    @29
    @2
    wph
    cB
    @29
    wss
    @0
    grpidssd.c
    adantr
    @24
    sseldd
    @6
    @28
    @30
    @36
    @31
    @32
    @29
    cM
    @3
    cX
    @33
    @35
    grpinvcl
    syl2anc
    @32
    @29
    @7
    cM
    @2
    @4
    cX
    @33
    @34
    grprcan
    syl13anc
    mpbid
    ex
end
