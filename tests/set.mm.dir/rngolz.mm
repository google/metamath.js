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
include "oveq1d.mm"
include "w3a.mm"
include "rngo0cl.mm"
include "simpr.mm"
include "3jca.mm"
include "rngodir.mm"
include "syldan.mm"
include "simpl.mm"
include "rngocl.mm"
include "syl3anc.mm"
include "grporid.mm"
include "eqcomd.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "wb.mm"
include "grpolcan.mm"
include "syl13anc.mm"
include "mpbid.mm"

theorem rngolz
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


  assert |- ( ( R e. RingOps /\ A e. X ) -> ( Z H A ) = Z )

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
    cZ
    cA
    cH
    co
    #
    @3
    cG
    co
    #
    @3
    cZ
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
    cZ
    cZ
    cG
    co
    #
    cA
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
    oveq1d
    @0
    @1
    @13
    @13
    @1
    w3a
    @9
    @4
    wceq
    @2
    @13
    @13
    @1
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
    @0
    @1
    simpr
    #
    3jca
    cZ
    cZ
    cA
    cR
    cG
    cH
    cX
    ringlz.3
    ringlz.4
    ringlz.2
    rngodir
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
    @2
    @0
    @13
    @1
    @16
    @0
    @1
    simpl
    @14
    @15
    cZ
    cA
    cR
    cG
    cH
    cX
    ringlz.3
    ringlz.4
    ringlz.2
    rngocl
    syl3anc
    #
    @11
    @16
    wa
    @5
    @3
    @3
    cZ
    cG
    cX
    ringlz.2
    ringlz.1
    grporid
    eqcomd
    syl2anc
    3eqtr3d
    @2
    @11
    @16
    @13
    @16
    @6
    @7
    wb
    @17
    @18
    @14
    @18
    @3
    cZ
    @3
    cG
    cX
    ringlz.2
    grpolcan
    syl13anc
    mpbid
end
