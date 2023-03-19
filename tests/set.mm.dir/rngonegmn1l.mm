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
include "jca.mm"
include "rngodir.mm"
include "3exp2.mm"
include "imp42.mm"
include "an32s.mm"
include "mpidan.mm"
include "eqid.mm"
include "rngoaddneg1.mm"
include "adantr.mm"
include "oveq1d.mm"
include "rngolz.mm"
include "eqtrd.mm"
include "rngolidm.mm"
include "3eqtr3rd.mm"
include "wb.mm"
include "rngocl.mm"
include "3expa.mm"
include "cgr.mm"
include "rngogrpo.mm"
include "grpoinvid1.mm"
include "syl3an1.mm"
include "mpd3an3.mm"
include "mpbird.mm"

theorem rngonegmn1l
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


  assert |- ( ( R e. RingOps /\ A e. X ) -> ( N ` A ) = ( ( N ` U ) H A ) )

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
    cU
    cN
    cfv
    #
    cA
    cH
    co
    #
    wceq
    #
    cA
    @4
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
    cU
    @3
    cG
    co
    #
    cA
    cH
    co
    #
    cU
    cA
    cH
    co
    #
    @4
    cG
    co
    #
    @7
    @6
    @0
    @1
    cU
    cX
    wcel
    #
    @3
    cX
    wcel
    #
    wa
    #
    @10
    @12
    wceq
    #
    @0
    @13
    @14
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
    @17
    ringneg.1
    rneqi
    eqtri
    #
    ringneg.2
    ringneg.5
    rngo1cl
    #
    @0
    @13
    @14
    @19
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
    #
    jca
    @0
    @15
    @1
    @16
    @0
    @13
    @14
    @1
    @16
    @0
    @13
    @14
    @1
    @16
    cU
    @3
    cA
    cR
    cG
    cH
    cX
    ringneg.1
    ringneg.2
    ringneg.3
    rngodir
    3exp2
    imp42
    an32s
    mpidan
    @2
    @10
    @7
    cA
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
    @13
    @21
    @19
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
    rngoaddneg1
    mpdan
    adantr
    oveq1d
    cA
    cR
    cG
    cH
    cX
    @7
    @22
    ringneg.3
    ringneg.1
    ringneg.2
    rngolz
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
    @18
    ringneg.5
    rngolidm
    oveq1d
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
    @14
    @23
    @20
    @0
    @14
    @1
    @23
    @0
    @14
    @1
    @23
    @3
    cA
    cR
    cG
    cH
    cX
    ringneg.1
    ringneg.2
    ringneg.3
    rngocl
    3expa
    an32s
    mpidan
    @0
    cG
    cgr
    wcel
    @1
    @23
    @24
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
    @22
    ringneg.4
    grpoinvid1
    syl3an1
    mpd3an3
    mpbird
end
