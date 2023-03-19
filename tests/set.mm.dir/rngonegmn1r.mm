include "crngo.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cgi.mm"
include "crn.mm"
include "c1st.mm"
include "rneqi.mm"
include "eqtri.mm"
include "rngo1cl.mm"
include "rngonegcl.mm"
include "mpdan.mm"
include "adantr.mm"
include "jca.mm"
include "rngodi.mm"
include "3exp2.mm"
include "imp43.mm"
include "eqid.mm"
include "rngoaddneg2.mm"
include "oveq2d.mm"
include "rngorz.mm"
include "eqtrd.mm"
include "rngoridm.mm"
include "3eqtr3rd.mm"
include "wb.mm"
include "rngocl.mm"
include "mpd3an3.mm"
include "cgr.mm"
include "rngogrpo.mm"
include "grpoinvid2.mm"
include "syl3an1.mm"
include "mpbird.mm"

theorem rngonegmn1r
  let cA: class A
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cN: class N
  let cX: class X
  assume ringneg.1: |- G = ( 1st ` R )
  assume ringneg.2: |- H = ( 2nd ` R )
  assume ringneg.3: |- X = ran G
  assume ringneg.4: |- N = ( inv ` G )
  assume ringneg.5: |- U = ( GId ` H )


  assert |- ( ( R e. RingOps /\ A e. X ) -> ( N ` A ) = ( A H ( N ` U ) ) )

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
    cN
    cfv
    cA
    cU
    cN
    cfv
    #
    cH
    co
    #
    wceq
    #
    @4
    cA
    cG
    co
    #
    cG
    cgi
    cfv
    #
    wceq
    #
    @2
    cA
    @3
    cU
    cG
    co
    #
    cH
    co
    #
    @4
    cA
    cU
    cH
    co
    #
    cG
    co
    #
    @7
    @6
    @2
    @3
    cX
    wcel
    #
    cU
    cX
    wcel
    #
    wa
    @10
    @12
    wceq
    #
    @2
    @13
    @14
    @0
    @13
    @1
    @0
    @14
    @13
    cR
    cU
    cH
    cX
    cX
    cG
    crn
    cR
    c1st
    cfv
    #
    crn
    ringneg.3
    cG
    @16
    ringneg.1
    rneqi
    eqtri
    #
    ringneg.2
    ringneg.5
    rngo1cl
    #
    cU
    cR
    cG
    cN
    cX
    ringneg.1
    ringneg.3
    ringneg.4
    rngonegcl
    mpdan
    adantr
    #
    @0
    @14
    @1
    @18
    adantr
    jca
    @0
    @1
    @13
    @14
    @15
    @0
    @1
    @13
    @14
    @15
    cA
    @3
    cU
    cR
    cG
    cH
    cX
    ringneg.1
    ringneg.2
    ringneg.3
    rngodi
    3exp2
    imp43
    mpdan
    @2
    @10
    cA
    @7
    cH
    co
    @7
    @2
    @9
    @7
    cA
    cH
    @0
    @9
    @7
    wceq
    #
    @1
    @0
    @14
    @20
    @18
    cU
    cR
    cG
    cN
    cX
    @7
    ringneg.1
    ringneg.3
    ringneg.4
    @7
    eqid
    #
    rngoaddneg2
    mpdan
    adantr
    oveq2d
    cA
    cR
    cG
    cH
    cX
    @7
    @21
    ringneg.3
    ringneg.1
    ringneg.2
    rngorz
    eqtrd
    @2
    @11
    cA
    @4
    cG
    cA
    cR
    cU
    cH
    cX
    ringneg.2
    @17
    ringneg.5
    rngoridm
    oveq2d
    3eqtr3rd
    @0
    @1
    @4
    cX
    wcel
    #
    @5
    @8
    wb
    #
    @0
    @1
    @13
    @22
    @19
    cA
    @3
    cR
    cG
    cH
    cX
    ringneg.1
    ringneg.2
    ringneg.3
    rngocl
    mpd3an3
    @0
    cG
    cgr
    wcel
    @1
    @22
    @23
    cR
    cG
    ringneg.1
    rngogrpo
    cA
    @4
    @7
    cG
    cN
    cX
    ringneg.3
    @21
    ringneg.4
    grpoinvid2
    syl3an1
    mpd3an3
    mpbird
end
