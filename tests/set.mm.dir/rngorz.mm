include "crngo.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cgr.mm"
include "rngogrpo.mm"
include "grpoidcl.mm"
include "grpolid.mm"
include "mpdan.mm"
include "syl.mm"
include "adantr.mm"
include "oveq2d.mm"
include "w3a.mm"
include "simpr.mm"
include "rngo0cl.mm"
include "3jca.mm"
include "rngodi.mm"
include "syldan.mm"
include "rngocl.mm"
include "mpd3an3.mm"
include "eqcomd.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "wb.mm"
include "grporcan.mm"
include "syl13anc.mm"
include "mpbid.mm"

theorem rngorz
  let cA: class A
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let cZ: class Z
  assume ringlz.1: |- Z = ( GId ` G )
  assume ringlz.2: |- X = ran G
  assume ringlz.3: |- G = ( 1st ` R )
  assume ringlz.4: |- H = ( 2nd ` R )


  assert |- ( ( R e. RingOps /\ A e. X ) -> ( A H Z ) = Z )

  proof
    cR
    crngo
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    cZ
    cH
    co
    #
    @3
    cG
    co
    #
    cZ
    @3
    cG
    co
    #
    wceq
    #
    @3
    cZ
    wceq
    #
    @2
    cA
    cZ
    cZ
    cG
    co
    #
    cH
    co
    #
    @3
    @4
    @5
    @2
    @8
    cZ
    cA
    cH
    @0
    @8
    cZ
    wceq
    #
    @1
    @0
    cG
    cgr
    wcel
    #
    @10
    cR
    cG
    ringlz.3
    rngogrpo
    #
    @11
    cZ
    cX
    wcel
    #
    @10
    cZ
    cG
    cX
    ringlz.2
    ringlz.1
    grpoidcl
    cZ
    cZ
    cG
    cX
    ringlz.2
    ringlz.1
    grpolid
    mpdan
    syl
    adantr
    oveq2d
    @0
    @1
    @1
    @13
    @13
    w3a
    @9
    @4
    wceq
    @2
    @1
    @13
    @13
    @0
    @1
    simpr
    @0
    @13
    @1
    cR
    cG
    cX
    cZ
    ringlz.3
    ringlz.2
    ringlz.1
    rngo0cl
    adantr
    #
    @14
    3jca
    cA
    cZ
    cZ
    cR
    cG
    cH
    cX
    ringlz.3
    ringlz.4
    ringlz.2
    rngodi
    syldan
    @2
    @11
    @3
    cX
    wcel
    #
    @3
    @5
    wceq
    @0
    @11
    @1
    @12
    adantr
    #
    @0
    @1
    @13
    @15
    @14
    cA
    cZ
    cR
    cG
    cH
    cX
    ringlz.3
    ringlz.4
    ringlz.2
    rngocl
    mpd3an3
    #
    @11
    @15
    wa
    @5
    @3
    @3
    cZ
    cG
    cX
    ringlz.2
    ringlz.1
    grpolid
    eqcomd
    syl2anc
    3eqtr3d
    @2
    @11
    @15
    @13
    @15
    @6
    @7
    wb
    @16
    @17
    @14
    @17
    @3
    cZ
    @3
    cG
    cX
    ringlz.2
    grporcan
    syl13anc
    mpbid
end
