include "cv.mm"
include "cdm.mm"
include "cdif.mm"
include "wcel.mm"
include "csn.mm"
include "cun.mm"
include "wfn.mm"
include "cfv.mm"
include "cpred.mm"
include "cres.mm"
include "wceq.mm"
include "wi.mm"
include "wfrlem13.mm"
include "weq.mm"
include "wo.mm"
include "elun.mm"
include "velsn.mm"
include "orbi2i.mm"
include "bitri.mm"
include "wa.mm"
include "wfrlem12.mm"
include "wfun.mm"
include "wb.mm"
include "fnfun.mm"
include "wss.mm"
include "cop.mm"
include "ssun1.mm"
include "sseqtr4i.mm"
include "w3a.mm"
include "funssfv.mm"
include "wfrdmcl.mm"
include "fun2ssres.mm"
include "syl3an3.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "mp3an2.mm"
include "sylan.mm"
include "syl5ibr.mm"
include "ex.mm"
include "pm2.43d.mm"
include "vsnid.mm"
include "elun2.mm"
include "ax-mp.mm"
include "reseq1i.mm"
include "resundir.mm"
include "c0.mm"
include "wfr.mm"
include "wn.mm"
include "wwe.mm"
include "wefr.mm"
include "predfrirr.mm"
include "ressnop0.mm"
include "mp2b.mm"
include "uneq2i.mm"
include "un0.mm"
include "eqtri.mm"
include "3eqtri.mm"
include "fveq2i.mm"
include "opeq2i.mm"
include "opex.mm"
include "elsn.mm"
include "mpbir.mm"
include "eleqtrri.mm"
include "fnopfvb.mm"
include "mpbiri.mm"
include "mpan2.mm"
include "fveq2.mm"
include "predeq3.mm"
include "reseq2d.mm"
include "syl5ibrcom.mm"
include "jaod.mm"
include "syl5bi.mm"
include "syl.mm"

theorem wfrlem14
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cR: class R
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vx: setvar x
  assume wfrlem13.1: |- R We A
  assume wfrlem13.2: |- R Se A
  assume wfrlem13.3: |- F = wrecs ( R , A , G )
  assume wfrlem13.4: |- C = ( F u. { <. z , ( G ` ( F |` Pred ( R , A , z ) ) ) >. } )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G y
  disjoint R y
  disjoint R z
  disjoint C y
  disjoint A f
  disjoint A x
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
  disjoint F f
  disjoint F x
  disjoint G f
  disjoint G x
  disjoint R f
  disjoint R x
  disjoint C f
  disjoint C x
  assert |- ( z e. ( A \ dom F ) -> ( y e. ( dom F u. { z } ) -> ( C ` y ) = ( G ` ( C |` Pred ( R , A , y ) ) ) ) )

  proof
    vz
    cv
    #
    cA
    cF
    cdm
    #
    cdif
    wcel
    cC
    @1
    @0
    csn
    #
    cun
    #
    wfn
    #
    vy
    cv
    #
    @3
    wcel
    #
    @5
    cC
    cfv
    #
    cC
    cA
    cR
    @5
    cpred
    #
    cres
    #
    cG
    cfv
    #
    wceq
    #
    wi
    vz
    cA
    cC
    cR
    cF
    cG
    wfrlem13.1
    wfrlem13.2
    wfrlem13.3
    wfrlem13.4
    wfrlem13
    @6
    @5
    @1
    wcel
    #
    vy
    vz
    weq
    #
    wo
    #
    @4
    @11
    @6
    @12
    @5
    @2
    wcel
    #
    wo
    @14
    @5
    @1
    @2
    elun
    @15
    @13
    @12
    vy
    @0
    velsn
    orbi2i
    bitri
    @4
    @12
    @11
    @13
    @4
    @12
    @11
    @4
    @12
    @12
    @11
    wi
    @12
    @11
    @4
    @12
    wa
    @5
    cF
    cfv
    #
    cF
    @8
    cres
    #
    cG
    cfv
    #
    wceq
    #
    vy
    cA
    cR
    cF
    cG
    wfrlem13.1
    wfrlem13.2
    wfrlem13.3
    wfrlem12
    @4
    cC
    wfun
    #
    @12
    @11
    @19
    wb
    #
    @3
    cC
    fnfun
    @20
    cF
    cC
    wss
    #
    @12
    @21
    cF
    cF
    @0
    cF
    cA
    cR
    @0
    cpred
    #
    cres
    #
    cG
    cfv
    #
    cop
    #
    csn
    #
    cun
    #
    cC
    cF
    @27
    ssun1
    wfrlem13.4
    sseqtr4i
    @20
    @22
    @12
    w3a
    #
    @7
    @16
    @10
    @18
    @5
    cC
    cF
    funssfv
    @29
    @9
    @17
    cG
    @12
    @20
    @22
    @8
    @1
    wss
    @9
    @17
    wceq
    cA
    cR
    cF
    cG
    @5
    wfrlem13.3
    wfrdmcl
    @8
    cC
    cF
    fun2ssres
    syl3an3
    fveq2d
    eqeq12d
    mp3an2
    sylan
    syl5ibr
    ex
    pm2.43d
    @4
    @11
    @13
    @0
    cC
    cfv
    #
    cC
    @23
    cres
    #
    cG
    cfv
    #
    wceq
    #
    @4
    @0
    @3
    wcel
    #
    @33
    @0
    @2
    wcel
    @34
    vz
    vsnid
    @0
    @2
    @1
    elun2
    ax-mp
    @4
    @34
    wa
    @33
    @0
    @32
    cop
    #
    cC
    wcel
    @35
    @28
    cC
    @35
    @27
    wcel
    #
    @35
    @28
    wcel
    @36
    @35
    @26
    wceq
    @32
    @25
    @0
    @31
    @24
    cG
    @31
    @28
    @23
    cres
    @24
    @27
    @23
    cres
    #
    cun
    #
    @24
    cC
    @28
    @23
    wfrlem13.4
    reseq1i
    cF
    @27
    @23
    resundir
    @38
    @24
    c0
    cun
    @24
    @37
    c0
    @24
    cA
    cR
    wfr
    #
    @0
    @23
    wcel
    wn
    @37
    c0
    wceq
    cA
    cR
    wwe
    @39
    wfrlem13.1
    cA
    cR
    wefr
    ax-mp
    cA
    cR
    @0
    predfrirr
    @0
    @25
    @23
    ressnop0
    mp2b
    uneq2i
    @24
    un0
    eqtri
    3eqtri
    fveq2i
    opeq2i
    @35
    @26
    @0
    @32
    opex
    elsn
    mpbir
    @35
    @27
    cF
    elun2
    ax-mp
    wfrlem13.4
    eleqtrri
    @3
    @0
    @32
    cC
    fnopfvb
    mpbiri
    mpan2
    @13
    @7
    @30
    @10
    @32
    @5
    @0
    cC
    fveq2
    @13
    @9
    @31
    cG
    @13
    @8
    @23
    cC
    cA
    cR
    @5
    @0
    predeq3
    reseq2d
    fveq2d
    eqeq12d
    syl5ibrcom
    jaod
    syl5bi
    syl
end
