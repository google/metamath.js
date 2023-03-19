include "c0g.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wcel.mm"
include "cv.mm"
include "wral.mm"
include "cgrp.mm"
include "eqid.mm"
include "grpidcl.mm"
include "syl.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "grplid.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "cbs.mm"
include "wb.mm"
include "sseldd.mm"
include "grpidlcan.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem grpidssd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cS: class S
  let cM: class M
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
  assert |- ( ph -> ( 0g ` M ) = ( 0g ` S ) )

  proof
    wph
    cS
    c0g
    cfv
    #
    cM
    c0g
    cfv
    #
    wph
    @0
    @0
    cM
    cplusg
    cfv
    #
    co
    #
    @0
    wceq
    #
    @0
    @1
    wceq
    #
    wph
    @3
    @0
    @0
    cS
    cplusg
    cfv
    #
    co
    #
    @0
    wph
    @0
    cB
    wcel
    #
    @8
    vx
    cv
    #
    vy
    cv
    #
    @2
    co
    #
    @9
    @10
    @6
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
    @3
    @7
    wceq
    #
    wph
    cS
    cgrp
    wcel
    #
    @8
    grpidssd.s
    cB
    cS
    @0
    grpidssd.b
    @0
    eqid
    #
    grpidcl
    syl
    #
    @17
    grpidssd.o
    @13
    @14
    @0
    @10
    @2
    co
    #
    @0
    @10
    @6
    co
    #
    wceq
    vx
    vy
    @0
    @0
    cB
    cB
    @9
    @0
    wceq
    @11
    @18
    @12
    @19
    @9
    @0
    @10
    @2
    oveq1
    @9
    @0
    @10
    @6
    oveq1
    eqeq12d
    @10
    @0
    wceq
    @18
    @3
    @19
    @7
    @10
    @0
    @0
    @2
    oveq2
    @10
    @0
    @0
    @6
    oveq2
    eqeq12d
    rspc2va
    syl21anc
    wph
    @15
    @8
    @7
    @0
    wceq
    grpidssd.s
    @17
    cB
    @6
    cS
    @0
    @0
    grpidssd.b
    @6
    eqid
    @16
    grplid
    syl2anc
    eqtrd
    wph
    cM
    cgrp
    wcel
    @0
    cM
    cbs
    cfv
    #
    wcel
    #
    @21
    @4
    @5
    wb
    grpidssd.m
    wph
    cB
    @20
    @0
    grpidssd.c
    @17
    sseldd
    #
    @22
    @20
    @2
    cM
    @0
    @1
    @0
    @20
    eqid
    @2
    eqid
    @1
    eqid
    grpidlcan
    syl3anc
    mpbid
    eqcomd
end
