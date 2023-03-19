include "cv.mm"
include "cdm.mm"
include "wcel.mm"
include "cop.mm"
include "wex.mm"
include "cfv.mm"
include "cpred.mm"
include "cres.mm"
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
include "cwrecs.mm"
include "df-wrecs.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "eluniab.mm"
include "bitri.mm"
include "abid.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "sylbir.mm"
include "wi.mm"
include "wel.mm"
include "fnop.mm"
include "ex.mm"
include "rsp.mm"
include "impcom.mm"
include "fndm.mm"
include "sseq2d.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "biimprd.mm"
include "expd.mm"
include "wfun.mm"
include "wfrfun.mm"
include "funssfv.mm"
include "3adant3l.mm"
include "fun2ssres.mm"
include "3adant3r.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "mp3an1.mm"
include "expcom.mm"
include "com23.mm"
include "syl6com.mm"
include "com34.mm"
include "sylcom.mm"
include "adantl.mm"
include "com14.mm"
include "syl7.mm"
include "exp4a.mm"
include "pm2.43d.mm"
include "syldc.mm"
include "3impd.mm"
include "exlimdv.mm"
include "mpdi.mm"
include "imp.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem wfrlem12
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vz: setvar z
  assume wfrfun.1: |- R We A
  assume wfrfun.2: |- R Se A
  assume wfrfun.3: |- F = wrecs ( R , A , G )

  disjoint A y
  disjoint G y
  disjoint R y
  disjoint F f
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint A z
  disjoint f g
  disjoint f h
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g h
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint h u
  disjoint h v
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint F z
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G x
  disjoint G z
  disjoint R f
  disjoint R g
  disjoint R h
  disjoint R x
  disjoint R z
  assert |- ( y e. dom F -> ( F ` y ) = ( G ` ( F |` Pred ( R , A , y ) ) ) )

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
    @9
    @5
    cres
    #
    cG
    cfv
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
    cwrecs
    @27
    wfrfun.3
    vx
    vy
    cA
    cR
    vf
    cG
    df-wrecs
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
    @23
    @9
    cF
    wss
    #
    @8
    @23
    @9
    @26
    wcel
    #
    @29
    @23
    vf
    abid
    @30
    @9
    @27
    cF
    @9
    @26
    elssuni
    @28
    syl6sseqr
    sylbir
    @10
    @22
    @29
    @8
    wi
    #
    vx
    @10
    @12
    @16
    @21
    @31
    @12
    @10
    vy
    vx
    wel
    #
    @16
    @21
    @31
    wi
    wi
    @12
    @10
    @32
    @11
    @0
    @1
    @9
    fnop
    ex
    @12
    @32
    @21
    @16
    @31
    @12
    @32
    @21
    @16
    @31
    wi
    #
    wi
    @12
    @32
    @32
    @21
    @33
    @32
    @21
    wa
    @20
    @12
    @32
    @33
    @21
    @32
    @20
    @20
    vy
    @11
    rsp
    impcom
    @16
    @32
    @20
    @12
    @31
    @15
    @32
    @20
    @12
    @31
    wi
    wi
    #
    wi
    @13
    @15
    @32
    @14
    @34
    @14
    vy
    @11
    rsp
    @32
    @14
    @12
    @20
    @31
    @32
    @14
    @12
    @20
    @31
    wi
    #
    @14
    @12
    wa
    @32
    @5
    @9
    cdm
    #
    wss
    #
    @0
    @36
    wcel
    #
    wa
    #
    @35
    @12
    @14
    @32
    @39
    wi
    @12
    @14
    @32
    @39
    @12
    @39
    @14
    @32
    wa
    @12
    @37
    @14
    @38
    @32
    @12
    @36
    @11
    @5
    @11
    @9
    fndm
    #
    sseq2d
    @12
    @36
    @11
    @0
    @40
    eleq2d
    anbi12d
    biimprd
    expd
    impcom
    @39
    @29
    @20
    @8
    @29
    @39
    @20
    @8
    wi
    #
    cF
    wfun
    #
    @29
    @39
    @41
    cA
    cR
    cF
    cG
    wfrfun.1
    wfrfun.2
    wfrfun.3
    wfrfun
    @42
    @29
    @39
    w3a
    #
    @8
    @20
    @43
    @4
    @17
    @7
    @19
    @42
    @29
    @38
    @4
    @17
    wceq
    @37
    @0
    cF
    @9
    funssfv
    3adant3l
    @43
    @6
    @18
    cG
    @42
    @29
    @37
    @6
    @18
    wceq
    @38
    @5
    cF
    @9
    fun2ssres
    3adant3r
    fveq2d
    eqeq12d
    biimprd
    mp3an1
    expcom
    com23
    syl6com
    expd
    com34
    sylcom
    adantl
    com14
    syl7
    exp4a
    pm2.43d
    com34
    syldc
    3impd
    exlimdv
    mpdi
    imp
    exlimiv
    sylbi
    exlimiv
    sylbi
end
