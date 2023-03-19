include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cin.mm"
include "cbs.mm"
include "cv.mm"
include "wi.mm"
include "cvv.mm"
include "eqid.mm"
include "cntzrcl.mm"
include "simprd.mm"
include "ressbasss.mm"
include "syl6ss.mm"
include "a1i.mm"
include "inss1.mm"
include "sseli.mm"
include "syl.mm"
include "wb.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "anass.mm"
include "elin.mm"
include "ressbas.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "ressplusg.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "ad2antrr.mm"
include "syl5rbbr.mm"
include "ssin.mm"
include "sseq2d.mm"
include "syl5bb.mm"
include "biimpd.mm"
include "impl.mm"
include "elcntz.mm"
include "ancom.mm"
include "bitri.mm"
include "adantl.mm"
include "anbi2d.mm"
include "3bitr4d.mm"
include "ex.mm"
include "pm5.21ndd.mm"
include "eqrdv.mm"

theorem resscntz
  let cA: class A
  let cS: class S
  let cG: class G
  let cH: class H
  let cV: class V
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume resscntz.p: |- H = ( G |`s A )
  assume resscntz.z: |- Z = ( Cntz ` G )
  assume resscntz.y: |- Y = ( Cntz ` H )


  assert |- ( ( A e. V /\ S C_ A ) -> ( Y ` S ) = ( ( Z ` S ) i^i A ) )

  proof
    cA
    cV
    wcel
    #
    cS
    cA
    wss
    #
    wa
    #
    vx
    cS
    cY
    cfv
    #
    cS
    cZ
    cfv
    #
    cA
    cin
    #
    @2
    cS
    cG
    cbs
    cfv
    #
    wss
    #
    vx
    cv
    #
    @3
    wcel
    #
    @8
    @5
    wcel
    #
    @9
    @7
    wi
    @2
    @9
    cS
    cH
    cbs
    cfv
    #
    @6
    @9
    cH
    cvv
    wcel
    cS
    @11
    wss
    #
    @11
    cS
    cH
    @8
    cY
    @11
    eqid
    #
    resscntz.y
    cntzrcl
    simprd
    cA
    @6
    cH
    cG
    resscntz.p
    @6
    eqid
    #
    ressbasss
    syl6ss
    a1i
    @10
    @7
    wi
    @2
    @10
    @8
    @4
    wcel
    #
    @7
    @5
    @4
    @8
    @4
    cA
    inss1
    sseli
    @15
    cG
    cvv
    wcel
    @7
    @6
    cS
    cG
    @8
    cZ
    @14
    resscntz.z
    cntzrcl
    simprd
    syl
    a1i
    @2
    @7
    @9
    @10
    wb
    @2
    @7
    wa
    #
    @8
    @11
    wcel
    #
    @8
    vy
    cv
    #
    cH
    cplusg
    cfv
    #
    co
    #
    @18
    @8
    @19
    co
    #
    wceq
    #
    vy
    cS
    wral
    #
    wa
    #
    @8
    cA
    wcel
    #
    @8
    @6
    wcel
    #
    @8
    @18
    cG
    cplusg
    cfv
    #
    co
    #
    @18
    @8
    @27
    co
    #
    wceq
    #
    vy
    cS
    wral
    #
    wa
    #
    wa
    #
    @9
    @10
    @33
    @25
    @26
    wa
    #
    @31
    wa
    #
    @16
    @24
    @25
    @26
    @31
    anass
    @0
    @35
    @24
    wb
    @1
    @7
    @0
    @34
    @17
    @31
    @23
    @34
    @8
    cA
    @6
    cin
    #
    wcel
    @0
    @17
    @8
    cA
    @6
    elin
    @0
    @36
    @11
    @8
    cA
    @6
    cH
    cV
    cG
    resscntz.p
    @14
    ressbas
    #
    eleq2d
    syl5bbr
    @0
    @30
    @22
    vy
    cS
    @0
    @28
    @20
    @29
    @21
    @0
    @27
    @19
    @8
    @18
    cA
    @27
    cG
    cH
    cV
    resscntz.p
    @27
    eqid
    #
    ressplusg
    #
    oveqd
    @0
    @27
    @19
    @18
    @8
    @39
    oveqd
    eqeq12d
    ralbidv
    anbi12d
    ad2antrr
    syl5rbbr
    @16
    @12
    @9
    @24
    wb
    @0
    @1
    @7
    @12
    @0
    @1
    @7
    wa
    #
    @12
    @40
    cS
    @36
    wss
    @0
    @12
    cS
    cA
    @6
    ssin
    @0
    @36
    @11
    cS
    @37
    sseq2d
    syl5bb
    biimpd
    impl
    vy
    @8
    @11
    @19
    cS
    cH
    cY
    @13
    @19
    eqid
    resscntz.y
    elcntz
    syl
    @10
    @25
    @15
    wa
    #
    @16
    @33
    @10
    @15
    @25
    wa
    @41
    @8
    @4
    cA
    elin
    @15
    @25
    ancom
    bitri
    @16
    @15
    @32
    @25
    @7
    @15
    @32
    wb
    @2
    vy
    @8
    @6
    @27
    cS
    cG
    cZ
    @14
    @38
    resscntz.z
    elcntz
    adantl
    anbi2d
    syl5bb
    3bitr4d
    ex
    pm5.21ndd
    eqrdv
end
