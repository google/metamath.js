include "cv.mm"
include "cdm.mm"
include "wcel.mm"
include "cop.mm"
include "wex.mm"
include "cfv.mm"
include "cpred.mm"
include "cres.mm"
include "co.mm"
include "wceq.mm"
include "vex.mm"
include "eldm2.mm"
include "wfn.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "w3a.mm"
include "cab.mm"
include "cuni.mm"
include "cfrecs.mm"
include "df-frecs.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "eluniab.mm"
include "bitri.mm"
include "wel.mm"
include "simpr3.mm"
include "simpr1.mm"
include "simpl.mm"
include "fnop.mm"
include "syl2anc.mm"
include "rsp.mm"
include "sylc.mm"
include "wfun.mm"
include "frrlem10.mm"
include "19.8a.mm"
include "abeq2i.mm"
include "sylibr.mm"
include "adantl.mm"
include "elssuni.mm"
include "syl.mm"
include "unieqi.mm"
include "eqtr4i.mm"
include "syl6sseqr.mm"
include "fndm.mm"
include "eleqtrrd.mm"
include "funssfv.mm"
include "mp3an2i.mm"
include "simpr2r.mm"
include "sseqtr4d.mm"
include "fun2ssres.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "exlimdv.mm"
include "imp.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem frrlem11
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let vf: setvar f
  let cF: class F
  let cG: class G
  let vz: setvar z
  assume frrlem10.1: |- R Fr A
  assume frrlem10.2: |- R Se A
  assume frrlem10.3: |- B = { f | E. x ( f Fn x /\ ( x C_ A /\ A. y e. x Pred ( R , A , y ) C_ x ) /\ A. y e. x ( f ` y ) = ( y G ( f |` Pred ( R , A , y ) ) ) ) }
  assume frrlem10.4: |- F = frecs ( R , A , G )

  disjoint F f
  disjoint x y
  disjoint A f
  disjoint A x
  disjoint A y
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint F x
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint B x
  disjoint A z
  disjoint F z
  disjoint G z
  disjoint R z
  disjoint x z
  disjoint y z
  disjoint f z
  assert |- ( y e. dom F -> ( F ` y ) = ( y G ( F |` Pred ( R , A , y ) ) ) )

  proof
    vy
    cv
    #
    cF
    cdm
    wcel
    @0
    vz
    cv
    #
    cop
    #
    cF
    wcel
    #
    vz
    wex
    @0
    cF
    cfv
    #
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
    co
    #
    wceq
    #
    vz
    @0
    cF
    vy
    vex
    eldm2
    @3
    @8
    vz
    @3
    @2
    vf
    cv
    #
    wcel
    #
    @9
    vx
    cv
    #
    wfn
    #
    @11
    cA
    wss
    #
    @5
    @11
    wss
    #
    vy
    @11
    wral
    #
    wa
    #
    @0
    @9
    cfv
    #
    @0
    @9
    @5
    cres
    #
    cG
    co
    #
    wceq
    #
    vy
    @11
    wral
    #
    w3a
    #
    vx
    wex
    #
    wa
    #
    vf
    wex
    #
    @8
    @3
    @2
    @23
    vf
    cab
    #
    cuni
    #
    wcel
    @25
    cF
    @27
    @2
    cF
    cA
    cR
    cG
    cfrecs
    @27
    frrlem10.4
    vx
    vy
    cA
    cR
    vf
    cG
    df-frecs
    eqtri
    #
    eleq2i
    @23
    vf
    @2
    eluniab
    bitri
    @24
    @8
    vf
    @10
    @23
    @8
    @10
    @22
    @8
    vx
    @10
    @22
    @8
    @10
    @22
    wa
    #
    @17
    @19
    @4
    @7
    @29
    @21
    vy
    vx
    wel
    #
    @20
    @10
    @12
    @16
    @21
    simpr3
    @29
    @12
    @10
    @30
    @10
    @12
    @16
    @21
    simpr1
    #
    @10
    @22
    simpl
    @11
    @0
    @1
    @9
    fnop
    syl2anc
    #
    @20
    vy
    @11
    rsp
    sylc
    cF
    wfun
    #
    @29
    @9
    cF
    wss
    #
    @0
    @9
    cdm
    #
    wcel
    @4
    @17
    wceq
    vx
    vy
    cA
    cB
    cR
    vf
    cF
    cG
    frrlem10.1
    frrlem10.2
    frrlem10.3
    frrlem10.4
    frrlem10
    #
    @29
    @9
    cB
    cuni
    #
    cF
    @29
    @9
    cB
    wcel
    #
    @9
    @37
    wss
    @22
    @38
    @10
    @22
    @23
    @38
    @22
    vx
    19.8a
    @23
    vf
    cB
    frrlem10.3
    abeq2i
    sylibr
    adantl
    @9
    cB
    elssuni
    syl
    cF
    @27
    @37
    @28
    cB
    @26
    frrlem10.3
    unieqi
    eqtr4i
    syl6sseqr
    #
    @29
    @0
    @11
    @35
    @32
    @29
    @12
    @35
    @11
    wceq
    @31
    @11
    @9
    fndm
    syl
    #
    eleqtrrd
    @0
    cF
    @9
    funssfv
    mp3an2i
    @29
    @6
    @18
    @0
    cG
    @33
    @29
    @34
    @5
    @35
    wss
    @6
    @18
    wceq
    @36
    @39
    @29
    @5
    @11
    @35
    @29
    @15
    @30
    @14
    @13
    @15
    @12
    @21
    @10
    simpr2r
    @32
    @14
    vy
    @11
    rsp
    sylc
    @40
    sseqtr4d
    @5
    cF
    @9
    fun2ssres
    mp3an2i
    oveq2d
    3eqtr4d
    ex
    exlimdv
    imp
    exlimiv
    sylbi
    exlimiv
    sylbi
end
